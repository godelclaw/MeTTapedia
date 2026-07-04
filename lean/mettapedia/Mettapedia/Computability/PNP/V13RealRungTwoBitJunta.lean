import Mettapedia.Computability.PNP.V13RealRungOneQRowBound

/-!
# PNP v13 real rung two: bit-junta and parity observers

This module opens the bit-level observer surface on the same linear public
instance `(A, A x)`.  It separates the kernel-flip half, which is already
available at bit level, from the remaining finite counting problem: bound the
maps for which the read RHS rows span-block the target coordinate.
-/

namespace Mettapedia.Computability.PNP

set_option autoImplicit false

/-- A `j`-junta over elementary public coordinates.  The decision may read at
most the listed coordinates, with repeated or unused slots allowed. -/
structure V13RealLinearBitJuntaObserver (m j : Nat) where
  coordinate : Fin j → Option (V13RealLinearPublicCoordinate m)
  decide : V13RealLinearPublic m → ZMod 2
  factorsThrough :
    ∀ public₀ public₁ : V13RealLinearPublic m,
      (∀ k : Fin j, ∀ coord : V13RealLinearPublicCoordinate m,
        coordinate k = some coord →
          v13RealLinearCoordinateValue coord public₀ =
            v13RealLinearCoordinateValue coord public₁) →
      decide public₀ = decide public₁

/-- RHS rows whose bits may affect a bit-junta under hidden-vector flips. -/
noncomputable def v13RealLinearBitJuntaRhsRows {m j : Nat}
    (observer : V13RealLinearBitJuntaObserver m j) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter
    (fun row : Fin m =>
      ∃ k : Fin j, observer.coordinate k = some (.rhs row))

theorem v13RealLinearBitJuntaRhsRows_mem {m j : Nat}
    (observer : V13RealLinearBitJuntaObserver m j) {row : Fin m} :
    row ∈ v13RealLinearBitJuntaRhsRows observer ↔
      ∃ k : Fin j, observer.coordinate k = some (.rhs row) := by
  classical
  simp [v13RealLinearBitJuntaRhsRows]

theorem v13RealLinearBitJuntaRhsRows_card_le {m j : Nat}
    (observer : V13RealLinearBitJuntaObserver m j) :
    (v13RealLinearBitJuntaRhsRows observer).card ≤ j := by
  classical
  let rows := v13RealLinearBitJuntaRhsRows observer
  let slot : {row : Fin m // row ∈ rows} → Fin j := fun row =>
    Classical.choose ((v13RealLinearBitJuntaRhsRows_mem observer).1 row.property)
  have hslot :
      ∀ row : {row : Fin m // row ∈ rows},
        observer.coordinate (slot row) = some (.rhs row.val) := by
    intro row
    exact Classical.choose_spec
      ((v13RealLinearBitJuntaRhsRows_mem observer).1 row.property)
  have hinj : Function.Injective slot := by
    intro row₀ row₁ h
    apply Subtype.ext
    have hcoord :
        some (V13RealLinearPublicCoordinate.rhs row₀.val) =
          some (V13RealLinearPublicCoordinate.rhs row₁.val) := by
      rw [← hslot row₀, h, hslot row₁]
    simpa using hcoord
  have hcard :
      Fintype.card {row : Fin m // row ∈ rows} ≤ Fintype.card (Fin j) :=
    Fintype.card_le_of_injective slot hinj
  simpa [rows] using hcard

/-- The RHS-row footprint as a rowset inside the junta read budget. -/
noncomputable def v13RealLinearBitJuntaRhsBudgetedRowset {m j : Nat}
    (observer : V13RealLinearBitJuntaObserver m j) :
    V13RealLinearBudgetedRowset m j :=
  ⟨v13RealLinearBitJuntaRhsRows observer,
    v13RealLinearBitJuntaRhsRows_card_le observer⟩

/-- A bit-junta is blocked for `(A, i₀)` exactly when the kernel common to all
RHS rows it reads forces the target bit to vanish. -/
def V13RealLinearBitJuntaBlocked {m j : Nat}
    (observer : V13RealLinearBitJuntaObserver m j)
    (A : V13F2LinearEquiv m) (i₀ : Fin m) : Prop :=
  V13RealLinearRowsBlockTarget A
    (v13RealLinearBitJuntaRhsRows observer) i₀

theorem v13RealLinearBitJunta_blocked_iff_kernel {m j : Nat}
    (observer : V13RealLinearBitJuntaObserver m j)
    (A : V13F2LinearEquiv m) (i₀ : Fin m) :
    V13RealLinearBitJuntaBlocked observer A i₀ ↔
      ∀ w : F2Vec m,
        (∀ row : Fin m,
          row ∈ v13RealLinearBitJuntaRhsRows observer →
            A.toEquiv w row = 0) →
          w i₀ = 0 :=
  Iff.rfl

theorem v13RealLinearBitJunta_blocked_iff_rowsGenerateTarget {m j : Nat}
    (observer : V13RealLinearBitJuntaObserver m j)
    (A : V13F2LinearEquiv m) (i₀ : Fin m) :
    V13RealLinearBitJuntaBlocked observer A i₀ ↔
      V13RealLinearRowsGenerateTarget A
        (v13RealLinearBitJuntaRhsRows observer) i₀ := by
  simpa [V13RealLinearBitJuntaBlocked] using
    (v13RealLinear_rowsBlockTarget_iff_rowsGenerateTarget A
      (v13RealLinearBitJuntaRhsRows observer) i₀)

/-- Explicit second-rung blocked-map allowance for `j` public-coordinate reads. -/
noncomputable def v13RealLinearBitJuntaEpsilon2 (j m : Nat) : Rat :=
  (4 * (2 : Rat) ^ j) / ((2 : Rat) ^ m)

theorem v13RealLinearBitJunta_coordinateValue_same_after_kernel_add
    {m j : Nat} (observer : V13RealLinearBitJuntaObserver m j)
    (A : V13F2LinearEquiv m) (x w : F2Vec m)
    (hkernel :
      ∀ row : Fin m, row ∈ v13RealLinearBitJuntaRhsRows observer →
        A.toEquiv w row = 0)
    {k : Fin j} {coord : V13RealLinearPublicCoordinate m}
    (hcoord : observer.coordinate k = some coord) :
    v13RealLinearCoordinateValue coord
        (v13RealLinearPublicInput
          ({ x := x, A := A } : V13RealLinearWorld m)) =
      v13RealLinearCoordinateValue coord
        (v13RealLinearPublicInput
          ({ x := f2AddVec x w, A := A } : V13RealLinearWorld m)) := by
  classical
  cases coord with
  | mapValue probe row =>
      simp [v13RealLinearCoordinateValue, v13RealLinearPublicInput]
  | inverseValue probe row =>
      simp [v13RealLinearCoordinateValue, v13RealLinearPublicInput]
  | rhs row =>
      have hmem : row ∈ v13RealLinearBitJuntaRhsRows observer := by
        rw [v13RealLinearBitJuntaRhsRows_mem observer]
        exact ⟨k, hcoord⟩
      have hrow : A.toEquiv w row = 0 := hkernel row hmem
      have hmap := congrFun (A.map_add x w) row
      simpa [v13RealLinearCoordinateValue, v13RealLinearPublicInput,
        f2AddVec, hrow] using hmap.symm

theorem v13RealLinearBitJunta_decide_same_after_kernel_add
    {m j : Nat} (observer : V13RealLinearBitJuntaObserver m j)
    (A : V13F2LinearEquiv m) (x w : F2Vec m)
    (hkernel :
      ∀ row : Fin m, row ∈ v13RealLinearBitJuntaRhsRows observer →
        A.toEquiv w row = 0) :
    observer.decide
        (v13RealLinearPublicInput
          ({ x := x, A := A } : V13RealLinearWorld m)) =
      observer.decide
        (v13RealLinearPublicInput
          ({ x := f2AddVec x w, A := A } : V13RealLinearWorld m)) := by
  exact observer.factorsThrough _ _
    (fun k coord hcoord =>
      v13RealLinearBitJunta_coordinateValue_same_after_kernel_add
        observer A x w hkernel hcoord)

def V13RealLinearBitJuntaFixedCorrect {m j : Nat}
    (observer : V13RealLinearBitJuntaObserver m j)
    (A : V13F2LinearEquiv m) (i₀ : Fin m) :=
  {x : F2Vec m //
    observer.decide
        (v13RealLinearPublicInput
          ({ x := x, A := A } : V13RealLinearWorld m)) =
      v13RealLinearTarget i₀
        ({ x := x, A := A } : V13RealLinearWorld m)}

def V13RealLinearBitJuntaFixedIncorrect {m j : Nat}
    (observer : V13RealLinearBitJuntaObserver m j)
    (A : V13F2LinearEquiv m) (i₀ : Fin m) :=
  {x : F2Vec m //
    observer.decide
        (v13RealLinearPublicInput
          ({ x := x, A := A } : V13RealLinearWorld m)) ≠
      v13RealLinearTarget i₀
        ({ x := x, A := A } : V13RealLinearWorld m)}

noncomputable instance {m j : Nat}
    (observer : V13RealLinearBitJuntaObserver m j)
    (A : V13F2LinearEquiv m) (i₀ : Fin m) :
    Fintype (V13RealLinearBitJuntaFixedCorrect observer A i₀) := by
  classical
  unfold V13RealLinearBitJuntaFixedCorrect
  infer_instance

noncomputable instance {m j : Nat}
    (observer : V13RealLinearBitJuntaObserver m j)
    (A : V13F2LinearEquiv m) (i₀ : Fin m) :
    Fintype (V13RealLinearBitJuntaFixedIncorrect observer A i₀) := by
  classical
  unfold V13RealLinearBitJuntaFixedIncorrect
  infer_instance

noncomputable def v13RealLinearBitJuntaFixedWorldCorrectIncorrectEquiv
    {m j : Nat} (observer : V13RealLinearBitJuntaObserver m j)
    (A : V13F2LinearEquiv m) (i₀ : Fin m) :
    F2Vec m ≃
      V13RealLinearBitJuntaFixedCorrect observer A i₀ ⊕
        V13RealLinearBitJuntaFixedIncorrect observer A i₀ where
  toFun x := by
    classical
    by_cases hcorrect :
        observer.decide
            (v13RealLinearPublicInput
              ({ x := x, A := A } : V13RealLinearWorld m)) =
          v13RealLinearTarget i₀
            ({ x := x, A := A } : V13RealLinearWorld m)
    · exact Sum.inl ⟨x, hcorrect⟩
    · exact Sum.inr ⟨x, hcorrect⟩
  invFun y :=
    Sum.elim
      (fun x : V13RealLinearBitJuntaFixedCorrect observer A i₀ => x.val)
      (fun x : V13RealLinearBitJuntaFixedIncorrect observer A i₀ => x.val)
      y
  left_inv x := by
    classical
    by_cases hcorrect :
        observer.decide
            (v13RealLinearPublicInput
              ({ x := x, A := A } : V13RealLinearWorld m)) =
          v13RealLinearTarget i₀
            ({ x := x, A := A } : V13RealLinearWorld m) <;>
      simp [hcorrect]
  right_inv y := by
    classical
    cases y with
    | inl x =>
        change
          (if hcorrect :
              observer.decide
                  (v13RealLinearPublicInput
                    ({ x := x.val, A := A } : V13RealLinearWorld m)) =
                v13RealLinearTarget i₀
                  ({ x := x.val, A := A } : V13RealLinearWorld m) then
              Sum.inl
                (⟨x.val, hcorrect⟩ :
                  V13RealLinearBitJuntaFixedCorrect observer A i₀)
            else
              Sum.inr
                (⟨x.val, hcorrect⟩ :
                  V13RealLinearBitJuntaFixedIncorrect observer A i₀)) =
            Sum.inl x
        rw [dif_pos x.property]
        rfl
    | inr x =>
        change
          (if hcorrect :
              observer.decide
                  (v13RealLinearPublicInput
                    ({ x := x.val, A := A } : V13RealLinearWorld m)) =
                v13RealLinearTarget i₀
                  ({ x := x.val, A := A } : V13RealLinearWorld m) then
              Sum.inl
                (⟨x.val, hcorrect⟩ :
                  V13RealLinearBitJuntaFixedCorrect observer A i₀)
            else
              Sum.inr
                (⟨x.val, hcorrect⟩ :
                  V13RealLinearBitJuntaFixedIncorrect observer A i₀)) =
            Sum.inr x
        rw [dif_neg x.property]
        rfl

theorem v13RealLinearBitJuntaFixedWorld_card_eq_correct_add_incorrect
    {m j : Nat} (observer : V13RealLinearBitJuntaObserver m j)
    (A : V13F2LinearEquiv m) (i₀ : Fin m) :
    Fintype.card (F2Vec m) =
      Fintype.card (V13RealLinearBitJuntaFixedCorrect observer A i₀) +
        Fintype.card (V13RealLinearBitJuntaFixedIncorrect observer A i₀) := by
  simpa [Fintype.card_sum] using
    Fintype.card_congr
      (v13RealLinearBitJuntaFixedWorldCorrectIncorrectEquiv observer A i₀)

noncomputable def v13RealLinearBitJunta_fixedCorrectIncorrectEquiv
    {m j : Nat} (observer : V13RealLinearBitJuntaObserver m j)
    (A : V13F2LinearEquiv m) (i₀ : Fin m)
    (w : F2Vec m) (hwi : w i₀ = 1)
    (hkernel :
      ∀ row : Fin m, row ∈ v13RealLinearBitJuntaRhsRows observer →
        A.toEquiv w row = 0) :
    V13RealLinearBitJuntaFixedCorrect observer A i₀ ≃
      V13RealLinearBitJuntaFixedIncorrect observer A i₀ where
  toFun x :=
    ⟨f2AddVec x.val w, by
      have hdec :=
        v13RealLinearBitJunta_decide_same_after_kernel_add
          observer A x.val w hkernel
      have htargetNe :
          v13RealLinearTarget i₀
              ({ x := f2AddVec x.val w, A := A } :
                V13RealLinearWorld m) ≠
            v13RealLinearTarget i₀
              ({ x := x.val, A := A } : V13RealLinearWorld m) :=
        v13RealLinear_target_changes_after_kernel_hit A x.val w hwi
      intro hbad
      apply htargetNe
      calc
        v13RealLinearTarget i₀
            ({ x := f2AddVec x.val w, A := A } :
              V13RealLinearWorld m) =
          observer.decide
            (v13RealLinearPublicInput
              ({ x := f2AddVec x.val w, A := A } :
                V13RealLinearWorld m)) := hbad.symm
        _ = observer.decide
            (v13RealLinearPublicInput
              ({ x := x.val, A := A } : V13RealLinearWorld m)) := hdec.symm
        _ = v13RealLinearTarget i₀
            ({ x := x.val, A := A } : V13RealLinearWorld m) := x.property⟩
  invFun x :=
    ⟨f2AddVec x.val w, by
      have hdec :=
        v13RealLinearBitJunta_decide_same_after_kernel_add
          observer A x.val w hkernel
      have htargetNe :
          v13RealLinearTarget i₀
              ({ x := f2AddVec x.val w, A := A } :
                V13RealLinearWorld m) ≠
            v13RealLinearTarget i₀
              ({ x := x.val, A := A } : V13RealLinearWorld m) :=
        v13RealLinear_target_changes_after_kernel_hit A x.val w hwi
      have hdecFlipped :
          observer.decide
              (v13RealLinearPublicInput
                ({ x := f2AddVec x.val w, A := A } :
                  V13RealLinearWorld m)) =
            observer.decide
              (v13RealLinearPublicInput
                ({ x := x.val, A := A } : V13RealLinearWorld m)) :=
        hdec.symm
      have hdecFlip_ne_targetOrig :
          observer.decide
              (v13RealLinearPublicInput
                ({ x := f2AddVec x.val w, A := A } :
                  V13RealLinearWorld m)) ≠
            v13RealLinearTarget i₀
              ({ x := x.val, A := A } : V13RealLinearWorld m) := by
        intro hbad
        exact x.property (hdecFlipped.symm.trans hbad)
      exact
        v13_zmod2_eq_of_ne_left htargetNe hdecFlip_ne_targetOrig⟩
  left_inv x := by
    apply Subtype.ext
    funext row
    exact f2_add_right_self (x.val row) (w row)
  right_inv x := by
    apply Subtype.ext
    funext row
    exact f2_add_right_self (x.val row) (w row)

theorem v13RealLinearBitJunta_correct_card_eq_incorrect_card_of_kernel_hit
    {m j : Nat} (observer : V13RealLinearBitJuntaObserver m j)
    (A : V13F2LinearEquiv m) (i₀ : Fin m)
    (w : F2Vec m) (hwi : w i₀ = 1)
    (hkernel :
      ∀ row : Fin m, row ∈ v13RealLinearBitJuntaRhsRows observer →
        A.toEquiv w row = 0) :
    Fintype.card (V13RealLinearBitJuntaFixedCorrect observer A i₀) =
      Fintype.card (V13RealLinearBitJuntaFixedIncorrect observer A i₀) :=
  Fintype.card_congr
    (v13RealLinearBitJunta_fixedCorrectIncorrectEquiv
      observer A i₀ w hwi hkernel)

theorem v13RealLinearBitJunta_correct_card_eq_incorrect_card_of_not_blocked
    {m j : Nat} (observer : V13RealLinearBitJuntaObserver m j)
    (A : V13F2LinearEquiv m) (i₀ : Fin m)
    (hnot : ¬ V13RealLinearBitJuntaBlocked observer A i₀) :
    Fintype.card (V13RealLinearBitJuntaFixedCorrect observer A i₀) =
      Fintype.card (V13RealLinearBitJuntaFixedIncorrect observer A i₀) := by
  rcases v13RealLinear_exists_kernel_hit_of_not_rowsBlockTarget
      (A := A) (rows := v13RealLinearBitJuntaRhsRows observer)
      (i₀ := i₀) hnot with
    ⟨w, hwi, hkernel⟩
  exact
    v13RealLinearBitJunta_correct_card_eq_incorrect_card_of_kernel_hit
      observer A i₀ w hwi hkernel

theorem
    v13RealLinearBitJunta_fixed_correct_card_mul_two_eq_f2vec_card_of_not_blocked
    {m j : Nat} (observer : V13RealLinearBitJuntaObserver m j)
    (A : V13F2LinearEquiv m) (i₀ : Fin m)
    (hnot : ¬ V13RealLinearBitJuntaBlocked observer A i₀) :
    Fintype.card (V13RealLinearBitJuntaFixedCorrect observer A i₀) * 2 =
      Fintype.card (F2Vec m) := by
  let C := Fintype.card (V13RealLinearBitJuntaFixedCorrect observer A i₀)
  let I := Fintype.card (V13RealLinearBitJuntaFixedIncorrect observer A i₀)
  have hci : C = I := by
    simpa [C, I] using
      v13RealLinearBitJunta_correct_card_eq_incorrect_card_of_not_blocked
        observer A i₀ hnot
  have hworld :
      Fintype.card (F2Vec m) = C + I := by
    simpa [C, I] using
      v13RealLinearBitJuntaFixedWorld_card_eq_correct_add_incorrect
        observer A i₀
  omega

noncomputable def v13RealLinearBitJuntaFixedSuccess
    {m j : Nat} (observer : V13RealLinearBitJuntaObserver m j)
    (A : V13F2LinearEquiv m) (i₀ : Fin m) : Rat :=
  (Fintype.card (V13RealLinearBitJuntaFixedCorrect observer A i₀) : Rat) /
    (Fintype.card (F2Vec m) : Rat)

theorem v13RealLinearBitJunta_fixedSuccess_eq_half_of_not_blocked
    {m j : Nat} (observer : V13RealLinearBitJuntaObserver m j)
    (A : V13F2LinearEquiv m) (i₀ : Fin m)
    (hnot : ¬ V13RealLinearBitJuntaBlocked observer A i₀) :
    v13RealLinearBitJuntaFixedSuccess observer A i₀ = (1 / 2 : Rat) := by
  classical
  unfold v13RealLinearBitJuntaFixedSuccess
  let C := Fintype.card (V13RealLinearBitJuntaFixedCorrect observer A i₀)
  let T := Fintype.card (F2Vec m)
  have hcardNat : C * 2 = T := by
    simpa [C, T] using
      v13RealLinearBitJunta_fixed_correct_card_mul_two_eq_f2vec_card_of_not_blocked
        observer A i₀ hnot
  have hcardRat : (C : Rat) * 2 = (T : Rat) := by
    exact_mod_cast hcardNat
  have hTposNat : 0 < T := by
    dsimp [T]
    rw [v13RealLinear_f2vec_card]
    positivity
  have hTpos : (0 : Rat) < (T : Rat) := by
    exact_mod_cast hTposNat
  change (C : Rat) / (T : Rat) = (1 / 2 : Rat)
  field_simp [hTpos.ne']
  linarith

/-- Fixed no-target fiber for a map satisfying the no-target admissibility
condition. -/
abbrev V13RealLinearNoTargetBitJuntaFixedCorrect {m j : Nat}
    (i₀ : Fin m) (observer : V13RealLinearBitJuntaObserver m j)
    (A : V13RealLinearNoTargetRowsMap m i₀) :=
  V13RealLinearBitJuntaFixedCorrect observer A.val i₀

abbrev V13RealLinearNoTargetBitJuntaFixedIncorrect {m j : Nat}
    (i₀ : Fin m) (observer : V13RealLinearBitJuntaObserver m j)
    (A : V13RealLinearNoTargetRowsMap m i₀) :=
  V13RealLinearBitJuntaFixedIncorrect observer A.val i₀

def V13RealLinearNoTargetBitJuntaBlockedMap {m j : Nat}
    (i₀ : Fin m) (observer : V13RealLinearBitJuntaObserver m j)
    (A : V13RealLinearNoTargetRowsMap m i₀) : Prop :=
  V13RealLinearBitJuntaBlocked observer A.val i₀

abbrev V13RealLinearNoTargetBitJuntaBlockedMapSet {m j : Nat}
    (i₀ : Fin m) (observer : V13RealLinearBitJuntaObserver m j) :=
  {A : V13RealLinearNoTargetRowsMap m i₀ //
    V13RealLinearNoTargetBitJuntaBlockedMap i₀ observer A}

noncomputable instance {m j : Nat}
    (i₀ : Fin m) (observer : V13RealLinearBitJuntaObserver m j) :
    Fintype (V13RealLinearNoTargetBitJuntaBlockedMapSet i₀ observer) := by
  classical
  unfold V13RealLinearNoTargetBitJuntaBlockedMapSet
  infer_instance

theorem v13RealLinearNoTargetBitJunta_blockedMap_iff_kernel
    {m j : Nat} (i₀ : Fin m)
    (observer : V13RealLinearBitJuntaObserver m j)
    (A : V13RealLinearNoTargetRowsMap m i₀) :
    V13RealLinearNoTargetBitJuntaBlockedMap i₀ observer A ↔
      ∀ w : F2Vec m,
        (∀ row : Fin m,
          row ∈ v13RealLinearBitJuntaRhsRows observer →
            A.val.toEquiv w row = 0) →
          w i₀ = 0 :=
  Iff.rfl

theorem v13RealLinearNoTargetBitJunta_blockedMap_iff_rowsGenerateTarget
    {m j : Nat} (i₀ : Fin m)
    (observer : V13RealLinearBitJuntaObserver m j)
    (A : V13RealLinearNoTargetRowsMap m i₀) :
    V13RealLinearNoTargetBitJuntaBlockedMap i₀ observer A ↔
      V13RealLinearRowsGenerateTarget A.val
        (v13RealLinearBitJuntaRhsBudgetedRowset observer).1 i₀ := by
  simpa [V13RealLinearNoTargetBitJuntaBlockedMap,
    v13RealLinearBitJuntaRhsBudgetedRowset] using
    (v13RealLinearBitJunta_blocked_iff_rowsGenerateTarget
      observer A.val i₀)

abbrev V13RealLinearNoTargetBudgetedRowsetGeneratingMapSet {m j : Nat}
    (i₀ : Fin m) (rows : V13RealLinearBudgetedRowset m j) :=
  {A : V13RealLinearNoTargetRowsMap m i₀ //
    V13RealLinearRowsGenerateTarget A.val rows.1 i₀}

noncomputable instance {m j : Nat} (i₀ : Fin m)
    (rows : V13RealLinearBudgetedRowset m j) :
    Fintype
      (V13RealLinearNoTargetBudgetedRowsetGeneratingMapSet i₀ rows) := by
  classical
  unfold V13RealLinearNoTargetBudgetedRowsetGeneratingMapSet
  infer_instance

noncomputable def
    v13RealLinearNoTargetBitJuntaBlockedMapSetEquivBudgetedGeneratingMapSet
    {m j : Nat} (i₀ : Fin m)
    (observer : V13RealLinearBitJuntaObserver m j) :
    V13RealLinearNoTargetBitJuntaBlockedMapSet i₀ observer ≃
      V13RealLinearNoTargetBudgetedRowsetGeneratingMapSet i₀
        (v13RealLinearBitJuntaRhsBudgetedRowset observer) where
  toFun A :=
    ⟨A.val,
      (v13RealLinearNoTargetBitJunta_blockedMap_iff_rowsGenerateTarget
        i₀ observer A.val).1 A.property⟩
  invFun A :=
    ⟨A.val,
      (v13RealLinearNoTargetBitJunta_blockedMap_iff_rowsGenerateTarget
        i₀ observer A.val).2 A.property⟩
  left_inv A := by
    apply Subtype.ext
    rfl
  right_inv A := by
    apply Subtype.ext
    rfl

theorem
    v13RealLinearNoTargetBitJuntaBlockedMapSet_card_eq_budgetedGeneratingMapSet
    {m j : Nat} (i₀ : Fin m)
    (observer : V13RealLinearBitJuntaObserver m j) :
    Fintype.card (V13RealLinearNoTargetBitJuntaBlockedMapSet i₀ observer) =
      Fintype.card
        (V13RealLinearNoTargetBudgetedRowsetGeneratingMapSet i₀
          (v13RealLinearBitJuntaRhsBudgetedRowset observer)) :=
  Fintype.card_congr
    (v13RealLinearNoTargetBitJuntaBlockedMapSetEquivBudgetedGeneratingMapSet
      i₀ observer)

/-- Rowset-counting form of the remaining bit-junta blocked-map obligation. -/
def V13RealLinearNoTargetBudgetedRowsetGenerationCountingBound
    (m j : Nat) : Prop :=
  ∀ i₀ : Fin m, ∀ rows : V13RealLinearBudgetedRowset m j,
    ((2 : Nat) ^ m) *
        Fintype.card
          (V13RealLinearNoTargetBudgetedRowsetGeneratingMapSet i₀ rows) ≤
      4 * ((2 : Nat) ^ j) *
        Fintype.card (V13RealLinearNoTargetRowsMap m i₀)

theorem
    V13RealLinearNoTargetBudgetedRowsetGenerationCountingBound_zeroBudget
    (m : Nat) :
    V13RealLinearNoTargetBudgetedRowsetGenerationCountingBound m 0 := by
  intro i₀ rows
  have hrows : rows.1.card = 0 := Nat.eq_zero_of_le_zero rows.2
  have hcard :
      Fintype.card
          (V13RealLinearNoTargetBudgetedRowsetGeneratingMapSet i₀ rows) =
        0 := by
    rw [Fintype.card_eq_zero_iff]
    refine ⟨?_⟩
    intro A
    exact
      v13RealLinear_not_rowsGenerateTarget_of_rows_card_zero
        A.val.val i₀ hrows A.property
  simp [hcard]

theorem
    V13RealLinearNoTargetBudgetedRowsetGenerationCountingBound_oneBudget
    (m : Nat) :
    V13RealLinearNoTargetBudgetedRowsetGenerationCountingBound m 1 := by
  intro i₀ rows
  have hcard :
      Fintype.card
          (V13RealLinearNoTargetBudgetedRowsetGeneratingMapSet i₀ rows) =
        0 := by
    rw [Fintype.card_eq_zero_iff]
    refine ⟨?_⟩
    intro A
    rcases Nat.eq_zero_or_pos rows.1.card with hzero | hpos
    · exact
        v13RealLinear_not_rowsGenerateTarget_of_rows_card_zero
          A.val.val i₀ hzero A.property
    · have hone : rows.1.card = 1 :=
        le_antisymm rows.2 (Nat.succ_le_of_lt hpos)
      rcases Finset.card_eq_one.mp hone with ⟨row, hrowsEq⟩
      have hgen :
          V13RealLinearRowsGenerateTarget A.val.val
            ({row} : Finset (Fin m)) i₀ := by
        simpa [hrowsEq] using A.property
      have htarget :
          ∀ w : F2Vec m, A.val.val.toEquiv w row = w i₀ :=
        (v13RealLinear_rowsGenerateTarget_singleton_iff
          A.val.val row i₀).1 hgen
      have hrowTarget :
          row ∈ V13RealLinearTargetRows A.val.val i₀ :=
        (v13RealLinear_mem_targetRows_iff A.val.val i₀ row).2 htarget
      have hrowNotTarget :
          row ∉ V13RealLinearTargetRows A.val.val i₀ := by
        rw [A.val.property]
        simp
      exact hrowNotTarget hrowTarget
  simp [hcard]

theorem
    v13RealLinearNoTargetRows_not_rowsGenerateTarget_of_rows_card_le_one
    {m : Nat} (i₀ : Fin m) (A : V13RealLinearNoTargetRowsMap m i₀)
    {rows : Finset (Fin m)} (hrows : rows.card ≤ 1) :
    ¬ V13RealLinearRowsGenerateTarget A.val rows i₀ := by
  classical
  intro hgen
  rcases Nat.eq_zero_or_pos rows.card with hzero | hpos
  · exact
      v13RealLinear_not_rowsGenerateTarget_of_rows_card_zero
        A.val i₀ hzero hgen
  · have hone : rows.card = 1 := le_antisymm hrows (Nat.succ_le_of_lt hpos)
    rcases Finset.card_eq_one.mp hone with ⟨row, hrowsEq⟩
    have hgenSingleton :
        V13RealLinearRowsGenerateTarget A.val
          ({row} : Finset (Fin m)) i₀ := by
      simpa [hrowsEq] using hgen
    have htarget :
        ∀ w : F2Vec m, A.val.toEquiv w row = w i₀ :=
      (v13RealLinear_rowsGenerateTarget_singleton_iff
        A.val row i₀).1 hgenSingleton
    have hrowTarget :
        row ∈ V13RealLinearTargetRows A.val i₀ :=
      (v13RealLinear_mem_targetRows_iff A.val i₀ row).2 htarget
    have hrowNotTarget :
        row ∉ V13RealLinearTargetRows A.val i₀ := by
      rw [A.property]
      simp
    exact hrowNotTarget hrowTarget

/-- The nonzero coefficients of a row-combination, recorded in the rowset
subtype so no extra row-membership transport is needed. -/
noncomputable def v13RealLinearRowCombinationSupport {m : Nat}
    {rows : Finset (Fin m)} (coeff : V13RealLinearRowCombination rows) :
    Finset {row : Fin m // row ∈ rows} := by
  classical
  exact Finset.univ.filter (fun row => coeff row ≠ 0)

theorem v13RealLinearRowCombinationSupport_mem {m : Nat}
    {rows : Finset (Fin m)} (coeff : V13RealLinearRowCombination rows)
    (row : {row : Fin m // row ∈ rows}) :
    row ∈ v13RealLinearRowCombinationSupport coeff ↔ coeff row ≠ 0 := by
  classical
  simp [v13RealLinearRowCombinationSupport]

theorem
    v13RealLinearNoTargetRowsTargetCoefficient_support_card_two_le
    {m : Nat} {rows : Finset (Fin m)} (i₀ : Fin m)
    (A : V13RealLinearNoTargetRowsMap m i₀)
    (coeff : V13RealLinearRowsTargetCoefficient A.val rows i₀) :
    2 ≤ (v13RealLinearRowCombinationSupport coeff.val).card := by
  classical
  let support := v13RealLinearRowCombinationSupport coeff.val
  change 2 ≤ support.card
  by_contra htwo
  have hlt : support.card < 2 := Nat.lt_of_not_ge htwo
  rcases Nat.eq_zero_or_pos support.card with hzero | hpos
  · have hsupportEmpty : support = ∅ := Finset.card_eq_zero.mp hzero
    have hcoeffZero : ∀ row : {row : Fin m // row ∈ rows},
        coeff.val row = 0 := by
      intro row
      by_contra hne
      have hmem : row ∈ support := by
        simpa [support] using
          (v13RealLinearRowCombinationSupport_mem coeff.val row).2 hne
      rw [hsupportEmpty] at hmem
      simp at hmem
    have hzeroEval :
        v13RealLinearRowCombinationEval A.val rows coeff.val
            (v13RealLinearSingleBit i₀) = 0 := by
      unfold v13RealLinearRowCombinationEval
      simp [hcoeffZero]
    have htarget := coeff.property (v13RealLinearSingleBit i₀)
    rw [hzeroEval] at htarget
    norm_num [v13RealLinearSingleBit] at htarget
  · have hleOne : support.card ≤ 1 := by
      exact Nat.lt_succ_iff.mp (by simpa using hlt)
    have hone : support.card = 1 :=
      le_antisymm hleOne (Nat.succ_le_of_lt hpos)
    rcases Finset.card_eq_one.mp hone with ⟨supportRow, hsupportEq⟩
    have hsupportMem : supportRow ∈ support := by
      simp [hsupportEq]
    have hsupportCoeffNonzero : coeff.val supportRow ≠ 0 := by
      simpa [support] using
        (v13RealLinearRowCombinationSupport_mem coeff.val supportRow).1
          hsupportMem
    have hsupportCoeffOne : coeff.val supportRow = 1 :=
      v13_zmod2_eq_one_of_ne_zero _ hsupportCoeffNonzero
    have hcoeffZero :
        ∀ row : {row : Fin m // row ∈ rows},
          row ≠ supportRow → coeff.val row = 0 := by
      intro row hne
      by_contra hnonzero
      have hmem : row ∈ support := by
        simpa [support] using
          (v13RealLinearRowCombinationSupport_mem coeff.val row).2 hnonzero
      have heq : row = supportRow := by
        simpa [hsupportEq] using hmem
      exact hne heq
    have htarget :
        ∀ w : F2Vec m, A.val.toEquiv w supportRow.val = w i₀ := by
      intro w
      have hsum :
          v13RealLinearRowCombinationEval A.val rows coeff.val w =
            coeff.val supportRow * A.val.toEquiv w supportRow.val := by
        unfold v13RealLinearRowCombinationEval
        refine Finset.sum_eq_single supportRow ?_ ?_
        · intro row _hrow hne
          simp [hcoeffZero row hne]
        · intro hnot
          exact False.elim (hnot (Finset.mem_univ supportRow))
      calc
        A.val.toEquiv w supportRow.val =
            coeff.val supportRow * A.val.toEquiv w supportRow.val := by
          rw [hsupportCoeffOne]
          simp
        _ = v13RealLinearRowCombinationEval A.val rows coeff.val w := hsum.symm
        _ = w i₀ := coeff.property w
    have hrowTarget :
        supportRow.val ∈ V13RealLinearTargetRows A.val i₀ :=
      (v13RealLinear_mem_targetRows_iff A.val i₀ supportRow.val).2 htarget
    have hrowNotTarget :
        supportRow.val ∉ V13RealLinearTargetRows A.val i₀ := by
      rw [A.property]
      simp
    exact hrowNotTarget hrowTarget

theorem
    v13RealLinearNoTargetBudgetedRowsetGeneratingMapSet_exists_twoSupport
    {m j : Nat} {i₀ : Fin m} {rows : V13RealLinearBudgetedRowset m j}
    (A : V13RealLinearNoTargetBudgetedRowsetGeneratingMapSet i₀ rows) :
    ∃ coeff : V13RealLinearRowsTargetCoefficient A.val.val rows.1 i₀,
      2 ≤ (v13RealLinearRowCombinationSupport coeff.val).card := by
  rcases A.property with ⟨coeff, hcoeff⟩
  refine ⟨⟨coeff, hcoeff⟩, ?_⟩
  exact
    v13RealLinearNoTargetRowsTargetCoefficient_support_card_two_le
      i₀ A.val ⟨coeff, hcoeff⟩

theorem
    v13RealLinearRowsTargetCoefficient_support_sum_target
    {m : Nat} {rows : Finset (Fin m)} (A : V13F2LinearEquiv m)
    (i₀ : Fin m)
    (coeff : V13RealLinearRowsTargetCoefficient A rows i₀) :
    ∀ w : F2Vec m,
      (v13RealLinearRowCombinationSupport coeff.val).sum
          (fun row => A.toEquiv w row.val) =
        w i₀ := by
  classical
  intro w
  let support := v13RealLinearRowCombinationSupport coeff.val
  let term : {row : Fin m // row ∈ rows} → ZMod 2 :=
    fun row => coeff.val row * A.toEquiv w row.val
  have hcoeffOne :
      ∀ row : {row : Fin m // row ∈ rows},
        row ∈ support → coeff.val row = 1 := by
    intro row hrow
    exact
      v13_zmod2_eq_one_of_ne_zero _
        ((v13RealLinearRowCombinationSupport_mem coeff.val row).1 hrow)
  have hcoeffZeroOfNotMem :
      ∀ row : {row : Fin m // row ∈ rows},
        row ∉ support → coeff.val row = 0 := by
    intro row hnot
    by_contra hnonzero
    exact hnot
      ((v13RealLinearRowCombinationSupport_mem coeff.val row).2 hnonzero)
  have hsumSupport :
      v13RealLinearRowCombinationEval A rows coeff.val w =
        support.sum term := by
    unfold v13RealLinearRowCombinationEval
    symm
    refine Finset.sum_subset (by intro row _hrow; simp) ?_
    intro row _hrow hrowNotSupport
    simp [hcoeffZeroOfNotMem row hrowNotSupport]
  have hsupportTerm :
      support.sum (fun row => A.toEquiv w row.val) =
        support.sum term := by
    apply Finset.sum_congr rfl
    intro row hrow
    simp [term, hcoeffOne row hrow]
  calc
    support.sum (fun row => A.toEquiv w row.val) =
        support.sum term := hsupportTerm
    _ = v13RealLinearRowCombinationEval A rows coeff.val w :=
      hsumSupport.symm
    _ = w i₀ := coeff.property w

theorem
    v13RealLinearNoTargetBudgetedRowsetGeneratingMapSet_exists_support_sum_target
    {m j : Nat} {i₀ : Fin m} {rows : V13RealLinearBudgetedRowset m j}
    (A : V13RealLinearNoTargetBudgetedRowsetGeneratingMapSet i₀ rows) :
    ∃ support : Finset {row : Fin m // row ∈ rows.1},
      2 ≤ support.card ∧ support.card ≤ j ∧
        ∀ w : F2Vec m,
          support.sum (fun row => A.val.val.toEquiv w row.val) = w i₀ := by
  classical
  rcases A.property with ⟨coeff, hcoeff⟩
  let targetCoeff : V13RealLinearRowsTargetCoefficient A.val.val rows.1 i₀ :=
    ⟨coeff, hcoeff⟩
  let support := v13RealLinearRowCombinationSupport targetCoeff.val
  have htwo : 2 ≤ support.card := by
    simpa [support, targetCoeff] using
      v13RealLinearNoTargetRowsTargetCoefficient_support_card_two_le
        i₀ A.val targetCoeff
  have hsupportLeSubtype :
      support.card ≤ Fintype.card {row : Fin m // row ∈ rows.1} :=
    Finset.card_le_univ support
  have hsupportLeRows : support.card ≤ rows.1.card := by
    simpa using hsupportLeSubtype
  refine ⟨support, htwo, hsupportLeRows.trans rows.2, ?_⟩
  exact
    v13RealLinearRowsTargetCoefficient_support_sum_target
      A.val.val i₀ targetCoeff

theorem
    v13RealLinearRowsTargetCoefficient_twoSupport_exists_pair_sum_target
    {m : Nat} {rows : Finset (Fin m)} (A : V13F2LinearEquiv m)
    (i₀ : Fin m)
    (coeff : V13RealLinearRowsTargetCoefficient A rows i₀)
    (hsupport :
      (v13RealLinearRowCombinationSupport coeff.val).card = 2) :
    ∃ row₀ row₁ : {row : Fin m // row ∈ rows},
      row₀ ≠ row₁ ∧
        ∀ w : F2Vec m,
          A.toEquiv w row₀.val + A.toEquiv w row₁.val = w i₀ := by
  classical
  let support := v13RealLinearRowCombinationSupport coeff.val
  have hsupportPos : 0 < support.card := by
    rw [hsupport]
    norm_num
  rcases Finset.card_pos.mp hsupportPos with ⟨row₀, hrow₀mem⟩
  let rest := support.erase row₀
  have hrestCard : rest.card = 1 := by
    dsimp [rest]
    rw [Finset.card_erase_of_mem hrow₀mem, hsupport]
  rcases Finset.card_eq_one.mp hrestCard with ⟨row₁, hrestEq⟩
  have hrow₁memRest : row₁ ∈ rest := by
    simp [rest, hrestEq]
  have hrow₁memSupport : row₁ ∈ support :=
    (Finset.mem_erase.mp hrow₁memRest).2
  have hrow₁ne₀ : row₁ ≠ row₀ :=
    (Finset.mem_erase.mp hrow₁memRest).1
  have hrow₀ne₁ : row₀ ≠ row₁ := hrow₁ne₀.symm
  have hcoeff₀Nonzero : coeff.val row₀ ≠ 0 := by
    simpa [support] using
      (v13RealLinearRowCombinationSupport_mem coeff.val row₀).1
        hrow₀mem
  have hcoeff₁Nonzero : coeff.val row₁ ≠ 0 := by
    simpa [support] using
      (v13RealLinearRowCombinationSupport_mem coeff.val row₁).1
        hrow₁memSupport
  have hcoeff₀ : coeff.val row₀ = 1 :=
    v13_zmod2_eq_one_of_ne_zero _ hcoeff₀Nonzero
  have hcoeff₁ : coeff.val row₁ = 1 :=
    v13_zmod2_eq_one_of_ne_zero _ hcoeff₁Nonzero
  have hcoeffZeroOfNotMem :
      ∀ row : {row : Fin m // row ∈ rows},
        row ∉ support → coeff.val row = 0 := by
    intro row hnot
    by_contra hnonzero
    exact hnot ((v13RealLinearRowCombinationSupport_mem coeff.val row).2
      hnonzero)
  refine ⟨row₀, row₁, hrow₀ne₁, ?_⟩
  intro w
  let term : {row : Fin m // row ∈ rows} → ZMod 2 :=
    fun row => coeff.val row * A.toEquiv w row.val
  have hsumSupport :
      v13RealLinearRowCombinationEval A rows coeff.val w =
        support.sum term := by
    unfold v13RealLinearRowCombinationEval
    symm
    refine Finset.sum_subset (by intro row _hrow; simp) ?_
    intro row _hrow hrowNotSupport
    simp [hcoeffZeroOfNotMem row hrowNotSupport]
  have hsumPair :
      support.sum term = A.toEquiv w row₀.val + A.toEquiv w row₁.val := by
    rw [← Finset.sum_erase_add (s := support) (a := row₀)
      (f := term) hrow₀mem]
    change rest.sum term + term row₀ =
      A.toEquiv w row₀.val + A.toEquiv w row₁.val
    rw [hrestEq]
    simp [term, hcoeff₀, hcoeff₁, add_comm]
  calc
    A.toEquiv w row₀.val + A.toEquiv w row₁.val =
        support.sum term := hsumPair.symm
    _ = v13RealLinearRowCombinationEval A rows coeff.val w :=
      hsumSupport.symm
    _ = w i₀ := coeff.property w

theorem
    v13RealLinearNoTargetTwoBudgetGeneratingMapSet_exists_pair_sum_target
    {m : Nat} {i₀ : Fin m} {rows : V13RealLinearBudgetedRowset m 2}
    (A : V13RealLinearNoTargetBudgetedRowsetGeneratingMapSet i₀ rows) :
    ∃ row₀ row₁ : {row : Fin m // row ∈ rows.1},
      row₀ ≠ row₁ ∧
        ∀ w : F2Vec m,
          A.val.val.toEquiv w row₀.val +
            A.val.val.toEquiv w row₁.val = w i₀ := by
  classical
  rcases A.property with ⟨coeff, hcoeff⟩
  let targetCoeff : V13RealLinearRowsTargetCoefficient A.val.val rows.1 i₀ :=
    ⟨coeff, hcoeff⟩
  let support := v13RealLinearRowCombinationSupport targetCoeff.val
  have hsupportTwoLe : 2 ≤ support.card := by
    simpa [support, targetCoeff] using
      (v13RealLinearNoTargetRowsTargetCoefficient_support_card_two_le
        i₀ A.val targetCoeff)
  have hsupportLeSubtype :
      support.card ≤ Fintype.card {row : Fin m // row ∈ rows.1} :=
    Finset.card_le_univ support
  have hsupportLeRows : support.card ≤ rows.1.card := by
    simpa using hsupportLeSubtype
  have hsupportLeTwo : support.card ≤ 2 :=
    hsupportLeRows.trans rows.2
  have hsupportEq : support.card = 2 :=
    le_antisymm hsupportLeTwo hsupportTwoLe
  exact
    v13RealLinearRowsTargetCoefficient_twoSupport_exists_pair_sum_target
      A.val.val i₀ targetCoeff (by simpa [support] using hsupportEq)

theorem
    v13RealLinearRowFunctionalTargetCosetHit_of_pair_sum_target
    {m : Nat} (A : V13F2LinearEquiv m) (i₀ row₀ row₁ : Fin m)
    (hpair : ∀ w : F2Vec m,
      A.toEquiv w row₀ + A.toEquiv w row₁ = w i₀) :
    V13RealLinearRowFunctionalTargetCosetHit A
      ({row₀} : Finset (Fin m)) i₀ row₁ := by
  classical
  refine ⟨v13RealLinearRowFunctional A row₀, ?_, ?_⟩
  · apply Submodule.subset_span
    exact ⟨⟨row₀, by simp⟩, rfl⟩
  · apply LinearMap.ext
    intro w
    have h := hpair w
    simpa [v13RealLinearTargetFunctional, v13RealLinearRowFunctional,
      add_comm] using h.symm

theorem
    v13RealLinearNoTargetTwoBudgetGeneratingMapSet_exists_pair_cosetHit
    {m : Nat} {i₀ : Fin m} {rows : V13RealLinearBudgetedRowset m 2}
    (A : V13RealLinearNoTargetBudgetedRowsetGeneratingMapSet i₀ rows) :
    ∃ row₀ row₁ : {row : Fin m // row ∈ rows.1},
      row₀ ≠ row₁ ∧ row₁.val ∉ ({row₀.val} : Finset (Fin m)) ∧
        V13RealLinearRowFunctionalTargetCosetHit A.val.val
          ({row₀.val} : Finset (Fin m)) i₀ row₁.val := by
  rcases
      v13RealLinearNoTargetTwoBudgetGeneratingMapSet_exists_pair_sum_target
        A with
    ⟨row₀, row₁, hne, hpair⟩
  have hrow₁NotMem : row₁.val ∉ ({row₀.val} : Finset (Fin m)) := by
    intro hmem
    have hval : row₁.val = row₀.val := by
      simpa using hmem
    exact hne.symm (Subtype.ext hval)
  exact
    ⟨row₀, row₁, hne, hrow₁NotMem,
      v13RealLinearRowFunctionalTargetCosetHit_of_pair_sum_target
        A.val.val i₀ row₀.val row₁.val hpair⟩

abbrev V13RealLinearNoTargetFixedPairSumTargetMapSet {m : Nat}
    (i₀ row₀ row₁ : Fin m) :=
  {A : V13RealLinearNoTargetRowsMap m i₀ //
    ∀ w : F2Vec m,
      A.val.toEquiv w row₀ + A.val.toEquiv w row₁ = w i₀}

noncomputable instance {m : Nat} (i₀ row₀ row₁ : Fin m) :
    Fintype (V13RealLinearNoTargetFixedPairSumTargetMapSet
      i₀ row₀ row₁) := by
  classical
  unfold V13RealLinearNoTargetFixedPairSumTargetMapSet
  infer_instance

abbrev V13RealLinearTwoRowZeroAt {m : Nat} (row₀ row₁ : Fin m) :=
  {s : F2Vec m // s row₀ = 0 ∧ s row₁ = 0}

noncomputable instance {m : Nat} (row₀ row₁ : Fin m) :
    Fintype (V13RealLinearTwoRowZeroAt row₀ row₁) := by
  classical
  unfold V13RealLinearTwoRowZeroAt
  infer_instance

noncomputable def v13RealLinearTwoRowZeroAtProdBitsEquiv {m : Nat}
    (row₀ row₁ : Fin m) (hneq : row₀ ≠ row₁) :
    V13RealLinearTwoRowZeroAt row₀ row₁ × (ZMod 2 × ZMod 2) ≃
      F2Vec m where
  toFun data :=
    fun row =>
      if row = row₀ then data.2.1
      else if row = row₁ then data.2.2
      else data.1.val row
  invFun w :=
    (⟨fun row =>
        if row = row₀ then 0 else if row = row₁ then 0 else w row,
      by
        constructor
        · simp
        · simp [hneq.symm]⟩,
      (w row₀, w row₁))
  left_inv data := by
    apply Prod.ext
    · apply Subtype.ext
      funext row
      by_cases hrow₀ : row = row₀
      · subst row
        simpa using data.1.property.1.symm
      · by_cases hrow₁ : row = row₁
        · subst row
          simpa using data.1.property.2.symm
        · simp [hrow₀, hrow₁]
    · apply Prod.ext
      · simp
      · simp [hneq.symm]
  right_inv w := by
    funext row
    by_cases hrow₀ : row = row₀
    · simp [hrow₀]
    · by_cases hrow₁ : row = row₁
      · subst row
        simp [hrow₀]
      · simp [hrow₀, hrow₁]

theorem v13RealLinearTwoRowZeroAt_card_mul_four {m : Nat}
    (row₀ row₁ : Fin m) (hneq : row₀ ≠ row₁) :
    Fintype.card (V13RealLinearTwoRowZeroAt row₀ row₁) * 4 =
      2 ^ m := by
  classical
  have hcard :=
    Fintype.card_congr
      (v13RealLinearTwoRowZeroAtProdBitsEquiv row₀ row₁ hneq)
  rw [Fintype.card_prod, Fintype.card_prod] at hcard
  simpa [F2Vec, Nat.mul_assoc] using hcard

def v13RealLinearTwoRowZeroShearSum {m : Nat}
    (row₀ row₁ : Fin m) (s : V13RealLinearTwoRowZeroAt row₀ row₁)
    (w : F2Vec m) : ZMod 2 :=
  (Finset.univ.erase row₁).sum (fun row => s.val row * w row)

theorem v13RealLinearTwoRowZeroShearSum_apply_shear {m : Nat}
    (row₀ row₁ : Fin m) (s : V13RealLinearTwoRowZeroAt row₀ row₁)
    (w : F2Vec m) :
    v13RealLinearTwoRowZeroShearSum row₀ row₁ s
        (fun row => if row = row₁ then
          w row₁ + v13RealLinearTwoRowZeroShearSum row₀ row₁ s w
        else w row) =
      v13RealLinearTwoRowZeroShearSum row₀ row₁ s w := by
  classical
  unfold v13RealLinearTwoRowZeroShearSum
  apply Finset.sum_congr rfl
  intro row hrow
  have hne : row ≠ row₁ := (Finset.mem_erase.mp hrow).1
  simp [hne]

def v13RealLinearTwoRowZeroShear {m : Nat}
    (row₀ row₁ : Fin m) (s : V13RealLinearTwoRowZeroAt row₀ row₁) :
    V13F2LinearEquiv m where
  toEquiv :=
    { toFun := fun w row =>
        if row = row₁ then
          w row₁ + v13RealLinearTwoRowZeroShearSum row₀ row₁ s w
        else w row
      invFun := fun w row =>
        if row = row₁ then
          w row₁ + v13RealLinearTwoRowZeroShearSum row₀ row₁ s w
        else w row
      left_inv := by
        intro w
        funext row
        by_cases hrow : row = row₁
        · subst row
          simp [v13RealLinearTwoRowZeroShearSum_apply_shear,
            f2_add_right_self]
        · simp [hrow]
      right_inv := by
        intro w
        funext row
        by_cases hrow : row = row₁
        · subst row
          simp [v13RealLinearTwoRowZeroShearSum_apply_shear,
            f2_add_right_self]
        · simp [hrow] }
  map_add := by
    intro x y
    funext row
    by_cases hrow : row = row₁
    · subst row
      unfold v13RealLinearTwoRowZeroShearSum
      simp [f2AddVec, Finset.sum_add_distrib, mul_add]
      ring
    · simp [f2AddVec, hrow]
  map_zero := by
    funext row
    by_cases hrow : row = row₁
    · subst row
      simp [f2ZeroVec, v13RealLinearTwoRowZeroShearSum]
    · simp [f2ZeroVec, hrow]

theorem v13RealLinearTwoRowZeroShear_apply_of_ne {m : Nat}
    (row₀ row₁ : Fin m) (s : V13RealLinearTwoRowZeroAt row₀ row₁)
    (w : F2Vec m) {row : Fin m} (hrow : row ≠ row₁) :
    (v13RealLinearTwoRowZeroShear row₀ row₁ s).toEquiv w row =
      w row := by
  simp [v13RealLinearTwoRowZeroShear, hrow]

theorem v13RealLinearTwoRowZeroShear_apply_row₁ {m : Nat}
    (row₀ row₁ : Fin m) (s : V13RealLinearTwoRowZeroAt row₀ row₁)
    (w : F2Vec m) :
    (v13RealLinearTwoRowZeroShear row₀ row₁ s).toEquiv w row₁ =
      w row₁ + v13RealLinearTwoRowZeroShearSum row₀ row₁ s w := by
  simp [v13RealLinearTwoRowZeroShear]

theorem v13RealLinearTwoRowZeroShearSum_singleBit
    {m : Nat} (row₀ row₁ : Fin m)
    (s : V13RealLinearTwoRowZeroAt row₀ row₁)
    {row : Fin m} (hrow : row ≠ row₁) :
    v13RealLinearTwoRowZeroShearSum row₀ row₁ s
        (v13RealLinearSingleBit row) =
      s.val row := by
  classical
  unfold v13RealLinearTwoRowZeroShearSum
  calc
    (Finset.univ.erase row₁).sum
        (fun j => s.val j * v13RealLinearSingleBit row j) =
      s.val row * v13RealLinearSingleBit row row := by
        refine Finset.sum_eq_single row ?_ ?_
        · intro j _hj hjne
          simp [v13RealLinearSingleBit, hjne]
        · intro hnot
          exact False.elim (hnot (by simp [hrow]))
    _ = s.val row := by simp [v13RealLinearSingleBit]

theorem v13RealLinearNoTargetFixedPairSumTarget_shear_targetRows_empty
    {m : Nat} (i₀ row₀ row₁ : Fin m) (hneq : row₀ ≠ row₁)
    (A : V13RealLinearNoTargetFixedPairSumTargetMapSet i₀ row₀ row₁)
    (s : V13RealLinearTwoRowZeroAt row₀ row₁) :
    V13RealLinearTargetRows
        (v13RealLinearComp
          (v13RealLinearTwoRowZeroShear row₀ row₁ s) A.val.val) i₀ =
      ∅ := by
  classical
  ext row
  constructor
  · intro htargetRow
    have htarget :
        ∀ w : F2Vec m,
          (v13RealLinearComp
              (v13RealLinearTwoRowZeroShear row₀ row₁ s) A.val.val).toEquiv
              w row = w i₀ :=
      (v13RealLinear_mem_targetRows_iff
        (v13RealLinearComp
          (v13RealLinearTwoRowZeroShear row₀ row₁ s) A.val.val)
        i₀ row).1 htargetRow
    by_cases hrow : row = row₁
    · subst row
      let probe : F2Vec m :=
        A.val.val.toEquiv.symm (v13RealLinearSingleBit row₀)
      have hArow₀ : A.val.val.toEquiv probe row₀ = 1 := by
        simp [probe, v13RealLinearSingleBit]
      have hArow₁ : A.val.val.toEquiv probe row₁ = 0 := by
        simp [probe, v13RealLinearSingleBit, hneq.symm]
      have hsum :
          v13RealLinearTwoRowZeroShearSum row₀ row₁ s
              (A.val.val.toEquiv probe) = 0 := by
        simpa [probe, s.property.1] using
          (v13RealLinearTwoRowZeroShearSum_singleBit
            row₀ row₁ s hneq)
      have hleft :
          (v13RealLinearComp
              (v13RealLinearTwoRowZeroShear row₀ row₁ s) A.val.val).toEquiv
              probe row₁ = 0 := by
        simp [v13RealLinearComp,
          v13RealLinearTwoRowZeroShear_apply_row₁, hArow₁, hsum]
      have htargetBit : probe i₀ = 1 := by
        have hpair := A.property probe
        simpa [hArow₀, hArow₁] using hpair.symm
      have hbad := htarget probe
      rw [hleft, htargetBit] at hbad
      norm_num at hbad
    · have htargetA : row ∈ V13RealLinearTargetRows A.val.val i₀ := by
        rw [v13RealLinear_mem_targetRows_iff]
        intro w
        have h := htarget w
        simpa [v13RealLinearComp,
          v13RealLinearTwoRowZeroShear_apply_of_ne row₀ row₁ s
            (A.val.val.toEquiv w) hrow] using h
      have hnot : row ∉ V13RealLinearTargetRows A.val.val i₀ := by
        rw [A.val.property]
        simp
      exact False.elim (hnot htargetA)
  · intro hrow
    simp at hrow

noncomputable def v13RealLinearNoTargetFixedPairSumTargetShear
    {m : Nat} (i₀ row₀ row₁ : Fin m) (hneq : row₀ ≠ row₁)
    (A : V13RealLinearNoTargetFixedPairSumTargetMapSet i₀ row₀ row₁)
    (s : V13RealLinearTwoRowZeroAt row₀ row₁) :
    V13RealLinearNoTargetRowsMap m i₀ :=
  ⟨v13RealLinearComp
      (v13RealLinearTwoRowZeroShear row₀ row₁ s) A.val.val,
    v13RealLinearNoTargetFixedPairSumTarget_shear_targetRows_empty
      i₀ row₀ row₁ hneq A s⟩

noncomputable def
    v13RealLinearNoTargetFixedPairSumTargetMapSetShearEmbedding
    {m : Nat} (i₀ row₀ row₁ : Fin m) (hneq : row₀ ≠ row₁) :
    V13RealLinearNoTargetFixedPairSumTargetMapSet i₀ row₀ row₁ ×
        V13RealLinearTwoRowZeroAt row₀ row₁ ↪
      V13RealLinearNoTargetRowsMap m i₀ where
  toFun pair :=
    v13RealLinearNoTargetFixedPairSumTargetShear
      i₀ row₀ row₁ hneq pair.1 pair.2
  inj' := by
    classical
    intro pair₀ pair₁ hmap
    rcases pair₀ with ⟨A₀, s₀⟩
    rcases pair₁ with ⟨A₁, s₁⟩
    have hB :
        v13RealLinearComp
            (v13RealLinearTwoRowZeroShear row₀ row₁ s₀) A₀.val.val =
          v13RealLinearComp
            (v13RealLinearTwoRowZeroShear row₀ row₁ s₁) A₁.val.val :=
      congrArg Subtype.val hmap
    have hrow_ne : row₀ ≠ row₁ := hneq
    have hrow₀Eq :
        ∀ w : F2Vec m,
          A₀.val.val.toEquiv w row₀ = A₁.val.val.toEquiv w row₀ := by
      intro w
      have h := congrFun (congrArg
        (fun A : V13F2LinearEquiv m => A.toEquiv w) hB) row₀
      simpa [v13RealLinearComp,
        v13RealLinearTwoRowZeroShear_apply_of_ne row₀ row₁ s₀
          (A₀.val.val.toEquiv w) hrow_ne,
        v13RealLinearTwoRowZeroShear_apply_of_ne row₀ row₁ s₁
          (A₁.val.val.toEquiv w) hrow_ne] using h
    have hrow₁Eq :
        ∀ w : F2Vec m,
          A₀.val.val.toEquiv w row₁ = A₁.val.val.toEquiv w row₁ := by
      intro w
      have hpair₀ := A₀.property w
      have hpair₁ := A₁.property w
      have h0 := hrow₀Eq w
      calc
        A₀.val.val.toEquiv w row₁ =
            A₀.val.val.toEquiv w row₀ +
              (A₀.val.val.toEquiv w row₀ +
                A₀.val.val.toEquiv w row₁) := by
                  calc
                    A₀.val.val.toEquiv w row₁ =
                        A₀.val.val.toEquiv w row₁ +
                          A₀.val.val.toEquiv w row₀ +
                          A₀.val.val.toEquiv w row₀ :=
                      (f2_add_right_self
                        (A₀.val.val.toEquiv w row₁)
                        (A₀.val.val.toEquiv w row₀)).symm
                    _ = A₀.val.val.toEquiv w row₀ +
                          (A₀.val.val.toEquiv w row₀ +
                            A₀.val.val.toEquiv w row₁) := by ring
        _ = A₀.val.val.toEquiv w row₀ + w i₀ := by rw [hpair₀]
        _ = A₁.val.val.toEquiv w row₀ + w i₀ := by rw [h0]
        _ = A₁.val.val.toEquiv w row₀ +
              (A₁.val.val.toEquiv w row₀ +
                A₁.val.val.toEquiv w row₁) := by rw [hpair₁]
        _ = A₁.val.val.toEquiv w row₁ := by
          calc
            A₁.val.val.toEquiv w row₀ +
                (A₁.val.val.toEquiv w row₀ +
                  A₁.val.val.toEquiv w row₁) =
              A₁.val.val.toEquiv w row₁ +
                A₁.val.val.toEquiv w row₀ +
                A₁.val.val.toEquiv w row₀ := by ring
            _ = A₁.val.val.toEquiv w row₁ :=
              f2_add_right_self
                (A₁.val.val.toEquiv w row₁)
                (A₁.val.val.toEquiv w row₀)
    have hAEq : A₀ = A₁ := by
      apply Subtype.ext
      apply Subtype.ext
      apply v13RealLinearEquiv_ext
      intro w
      funext row
      by_cases hrow : row = row₁
      · subst row
        exact hrow₁Eq w
      · have h := congrFun (congrArg
          (fun A : V13F2LinearEquiv m => A.toEquiv w) hB) row
        simpa [v13RealLinearComp,
          v13RealLinearTwoRowZeroShear_apply_of_ne row₀ row₁ s₀
            (A₀.val.val.toEquiv w) hrow,
          v13RealLinearTwoRowZeroShear_apply_of_ne row₀ row₁ s₁
            (A₁.val.val.toEquiv w) hrow] using h
    subst A₁
    have hs : s₀ = s₁ := by
      apply Subtype.ext
      funext row
      by_cases hrow₀ : row = row₀
      · subst row
        rw [s₀.property.1, s₁.property.1]
      · by_cases hrow₁ : row = row₁
        · subst row
          rw [s₀.property.2, s₁.property.2]
        · let probe : F2Vec m :=
            A₀.val.val.toEquiv.symm (v13RealLinearSingleBit row)
          have h := congrFun (congrArg
            (fun A : V13F2LinearEquiv m => A.toEquiv probe) hB) row₁
          have hsum₀ :
              v13RealLinearTwoRowZeroShearSum row₀ row₁ s₀
                  (A₀.val.val.toEquiv probe) = s₀.val row := by
            simpa [probe] using
              (v13RealLinearTwoRowZeroShearSum_singleBit
                row₀ row₁ s₀ hrow₁)
          have hsum₁ :
              v13RealLinearTwoRowZeroShearSum row₀ row₁ s₁
                  (A₀.val.val.toEquiv probe) = s₁.val row := by
            simpa [probe] using
              (v13RealLinearTwoRowZeroShearSum_singleBit
                row₀ row₁ s₁ hrow₁)
          simpa [v13RealLinearComp,
            v13RealLinearTwoRowZeroShear_apply_row₁,
            hsum₀, hsum₁] using h
    subst s₁
    rfl

theorem
    v13RealLinearNoTargetFixedPairSumTargetMapSet_card_mul_two_pow_le_noTarget
    {m : Nat} (i₀ row₀ row₁ : Fin m) (hneq : row₀ ≠ row₁) :
    Fintype.card
        (V13RealLinearNoTargetFixedPairSumTargetMapSet i₀ row₀ row₁) *
      2 ^ m ≤
    4 * Fintype.card (V13RealLinearNoTargetRowsMap m i₀) := by
  classical
  let S :=
    Fintype.card
      (V13RealLinearNoTargetFixedPairSumTargetMapSet i₀ row₀ row₁)
  let Z := Fintype.card (V13RealLinearTwoRowZeroAt row₀ row₁)
  let N := Fintype.card (V13RealLinearNoTargetRowsMap m i₀)
  have hSZ : S * Z ≤ N := by
    simpa [S, Z, N, Fintype.card_prod] using
      Fintype.card_le_of_embedding
        (v13RealLinearNoTargetFixedPairSumTargetMapSetShearEmbedding
          i₀ row₀ row₁ hneq)
  have hZ : Z * 4 = 2 ^ m := by
    simpa [Z] using
      v13RealLinearTwoRowZeroAt_card_mul_four row₀ row₁ hneq
  calc
    S * 2 ^ m = S * (Z * 4) := by rw [hZ]
    _ = 4 * (S * Z) := by ring
    _ ≤ 4 * N := Nat.mul_le_mul_left 4 hSZ

abbrev V13RealLinearNoTargetTwoBudgetPairSumWitnessSigma {m : Nat}
    (i₀ : Fin m) (rows : V13RealLinearBudgetedRowset m 2) :=
  Σ row₀ : {row : Fin m // row ∈ rows.1},
    Σ row₁ : {row : Fin m // row ∈ rows.1},
      {_A : V13RealLinearNoTargetFixedPairSumTargetMapSet
          i₀ row₀.val row₁.val // row₀ ≠ row₁}

noncomputable instance {m : Nat} (i₀ : Fin m)
    (rows : V13RealLinearBudgetedRowset m 2) :
    Fintype
      (V13RealLinearNoTargetTwoBudgetPairSumWitnessSigma i₀ rows) := by
  classical
  unfold V13RealLinearNoTargetTwoBudgetPairSumWitnessSigma
  infer_instance

noncomputable def
    v13RealLinearNoTargetTwoBudgetGeneratingMapSetEmbeddingPairSumSigma
    {m : Nat} (i₀ : Fin m) (rows : V13RealLinearBudgetedRowset m 2) :
    V13RealLinearNoTargetBudgetedRowsetGeneratingMapSet i₀ rows ↪
      V13RealLinearNoTargetTwoBudgetPairSumWitnessSigma i₀ rows where
  toFun A := by
    classical
    let ex :=
      v13RealLinearNoTargetTwoBudgetGeneratingMapSet_exists_pair_sum_target
        A
    let row₀ := Classical.choose ex
    let ex₁ := Classical.choose_spec ex
    let row₁ := Classical.choose ex₁
    let spec := Classical.choose_spec ex₁
    exact ⟨row₀, ⟨row₁, ⟨⟨A.val, spec.2⟩, spec.1⟩⟩⟩
  inj' := by
    intro A₀ A₁ h
    apply Subtype.ext
    exact congrArg
      (fun data : V13RealLinearNoTargetTwoBudgetPairSumWitnessSigma i₀ rows =>
        data.2.2.val.val) h

theorem
    v13RealLinearNoTargetTwoBudgetPairSumWitnessSigma_card_mul_two_pow_le
    {m : Nat} (i₀ : Fin m) (rows : V13RealLinearBudgetedRowset m 2) :
    Fintype.card
        (V13RealLinearNoTargetTwoBudgetPairSumWitnessSigma i₀ rows) *
      2 ^ m ≤
    16 * Fintype.card (V13RealLinearNoTargetRowsMap m i₀) := by
  classical
  let Row := {row : Fin m // row ∈ rows.1}
  let R := Fintype.card Row
  let N := Fintype.card (V13RealLinearNoTargetRowsMap m i₀)
  let M := 2 ^ m
  have hRle : R ≤ 2 := by
    simpa [R, Row] using rows.2
  have hterm :
      ∀ row₀ row₁ : Row,
        Fintype.card
            {A : V13RealLinearNoTargetFixedPairSumTargetMapSet
                i₀ row₀.val row₁.val // row₀ ≠ row₁} *
          M ≤ 4 * N := by
    intro row₀ row₁
    by_cases hneq : row₀ ≠ row₁
    · have hsub :
        Fintype.card
              {A : V13RealLinearNoTargetFixedPairSumTargetMapSet
                  i₀ row₀.val row₁.val // row₀ ≠ row₁} ≤
            Fintype.card
              (V13RealLinearNoTargetFixedPairSumTargetMapSet
                i₀ row₀.val row₁.val) :=
        Fintype.card_subtype_le
          (fun _A : V13RealLinearNoTargetFixedPairSumTargetMapSet
              i₀ row₀.val row₁.val => row₀ ≠ row₁)
      have hfixed :
          Fintype.card
              (V13RealLinearNoTargetFixedPairSumTargetMapSet
                i₀ row₀.val row₁.val) *
            M ≤ 4 * N := by
        have hval : row₀.val ≠ row₁.val := fun h =>
          hneq (Subtype.ext h)
        simpa [M, N] using
          v13RealLinearNoTargetFixedPairSumTargetMapSet_card_mul_two_pow_le_noTarget
            i₀ row₀.val row₁.val hval
      exact (Nat.mul_le_mul_right M hsub).trans hfixed
    · have hzero :
          Fintype.card
              {A : V13RealLinearNoTargetFixedPairSumTargetMapSet
                  i₀ row₀.val row₁.val // row₀ ≠ row₁} = 0 := by
        rw [Fintype.card_eq_zero_iff]
        refine ⟨?_⟩
        intro A
        exact hneq A.property
      simp [hzero]
  have hinner :
      ∀ row₀ : Row,
        Fintype.card
            (Σ row₁ : Row,
              {A : V13RealLinearNoTargetFixedPairSumTargetMapSet
                  i₀ row₀.val row₁.val // row₀ ≠ row₁}) *
          M ≤ R * (4 * N) := by
    intro row₀
    rw [Fintype.card_sigma]
    rw [Finset.sum_mul]
    calc
      (∑ row₁ : Row,
          Fintype.card
              {A : V13RealLinearNoTargetFixedPairSumTargetMapSet
                  i₀ row₀.val row₁.val // row₀ ≠ row₁} *
            M) ≤
          ∑ _row₁ : Row, 4 * N := by
            apply Finset.sum_le_sum
            intro row₁ _hrow₁
            exact hterm row₀ row₁
      _ = R * (4 * N) := by
        rw [Finset.sum_const]
        simp [R]
  change
    Fintype.card
        (Σ row₀ : Row,
          Σ row₁ : Row,
            {A : V13RealLinearNoTargetFixedPairSumTargetMapSet
                i₀ row₀.val row₁.val // row₀ ≠ row₁}) *
      M ≤ 16 * N
  let W :=
    Σ row₀ : Row,
      Σ row₁ : Row,
        {A : V13RealLinearNoTargetFixedPairSumTargetMapSet
            i₀ row₀.val row₁.val // row₀ ≠ row₁}
  change Fintype.card W * M ≤ 16 * N
  have hcardW :
      Fintype.card W =
        ∑ row₀ : Row,
          Fintype.card
            (Σ row₁ : Row,
              {A : V13RealLinearNoTargetFixedPairSumTargetMapSet
                  i₀ row₀.val row₁.val // row₀ ≠ row₁}) := by
    dsimp [W]
    exact Fintype.card_sigma
  rw [hcardW]
  rw [Finset.sum_mul]
  calc
    (∑ row₀ : Row,
        Fintype.card
            (Σ row₁ : Row,
              {A : V13RealLinearNoTargetFixedPairSumTargetMapSet
                  i₀ row₀.val row₁.val // row₀ ≠ row₁}) *
          M) ≤
        ∑ _row₀ : Row, R * (4 * N) := by
          apply Finset.sum_le_sum
          intro row₀ _hrow₀
          exact hinner row₀
    _ = R * (R * (4 * N)) := by
      rw [Finset.sum_const]
      simp [R]
    _ = (R * R) * (4 * N) := by ring
    _ ≤ 4 * (4 * N) := by
      exact Nat.mul_le_mul_right (4 * N)
        (Nat.mul_le_mul hRle hRle)
    _ = 16 * N := by ring

theorem
    V13RealLinearNoTargetBudgetedRowsetGenerationCountingBound_twoBudget
    (m : Nat) :
    V13RealLinearNoTargetBudgetedRowsetGenerationCountingBound m 2 := by
  intro i₀ rows
  let G := V13RealLinearNoTargetBudgetedRowsetGeneratingMapSet i₀ rows
  let W := V13RealLinearNoTargetTwoBudgetPairSumWitnessSigma i₀ rows
  let N := Fintype.card (V13RealLinearNoTargetRowsMap m i₀)
  let M := 2 ^ m
  have hG : Fintype.card G ≤ Fintype.card W :=
    Fintype.card_le_of_embedding
      (v13RealLinearNoTargetTwoBudgetGeneratingMapSetEmbeddingPairSumSigma
        i₀ rows)
  have hW : Fintype.card W * M ≤ 16 * N := by
    simpa [W, M, N] using
      v13RealLinearNoTargetTwoBudgetPairSumWitnessSigma_card_mul_two_pow_le
        i₀ rows
  calc
    M * Fintype.card G = Fintype.card G * M := by ring
    _ ≤ Fintype.card W * M := Nat.mul_le_mul_right M hG
    _ ≤ 16 * N := hW
    _ = 4 * 2 ^ 2 * N := by norm_num

abbrev V13RealLinearNoTargetFixedSupportSumTargetMapSet
    {m : Nat} {rows : Finset (Fin m)} (i₀ : Fin m)
    (support : Finset {row : Fin m // row ∈ rows}) :=
  {A : V13RealLinearNoTargetRowsMap m i₀ //
    ∀ w : F2Vec m,
      support.sum (fun row => A.val.toEquiv w row.val) = w i₀}

noncomputable instance {m : Nat} {rows : Finset (Fin m)}
    (i₀ : Fin m) (support : Finset {row : Fin m // row ∈ rows}) :
    Fintype
      (V13RealLinearNoTargetFixedSupportSumTargetMapSet i₀ support) := by
  classical
  unfold V13RealLinearNoTargetFixedSupportSumTargetMapSet
  infer_instance

theorem
    v13RealLinearNoTargetFixedSupportSumTarget_shear_targetRows_empty
    {m : Nat} {rows : Finset (Fin m)} (i₀ : Fin m)
    {support : Finset {row : Fin m // row ∈ rows}}
    (row₀ row₁ : {row : Fin m // row ∈ rows})
    (hrow₀ : row₀ ∈ support) (_hrow₁ : row₁ ∈ support)
    (hneq : row₀ ≠ row₁)
    (A : V13RealLinearNoTargetFixedSupportSumTargetMapSet i₀ support)
    (s : V13RealLinearTwoRowZeroAt row₀.val row₁.val) :
    V13RealLinearTargetRows
        (v13RealLinearComp
          (v13RealLinearTwoRowZeroShear row₀.val row₁.val s)
          A.val.val) i₀ =
      ∅ := by
  classical
  have hneqVal : row₀.val ≠ row₁.val := fun h => hneq (Subtype.ext h)
  ext row
  constructor
  · intro htargetRow
    have htarget :
        ∀ w : F2Vec m,
          (v13RealLinearComp
              (v13RealLinearTwoRowZeroShear row₀.val row₁.val s)
              A.val.val).toEquiv w row = w i₀ :=
      (v13RealLinear_mem_targetRows_iff
        (v13RealLinearComp
          (v13RealLinearTwoRowZeroShear row₀.val row₁.val s)
          A.val.val)
        i₀ row).1 htargetRow
    by_cases hrow : row = row₁.val
    · subst row
      let probe : F2Vec m :=
        A.val.val.toEquiv.symm (v13RealLinearSingleBit row₀.val)
      have hArow₀ : A.val.val.toEquiv probe row₀.val = 1 := by
        simp [probe, v13RealLinearSingleBit]
      have hArow₁ : A.val.val.toEquiv probe row₁.val = 0 := by
        simp [probe, v13RealLinearSingleBit, hneqVal.symm]
      have hsum :
          v13RealLinearTwoRowZeroShearSum row₀.val row₁.val s
              (A.val.val.toEquiv probe) = 0 := by
        simpa [probe, s.property.1] using
          (v13RealLinearTwoRowZeroShearSum_singleBit
            row₀.val row₁.val s hneqVal)
      have hleft :
          (v13RealLinearComp
              (v13RealLinearTwoRowZeroShear row₀.val row₁.val s)
              A.val.val).toEquiv probe row₁.val = 0 := by
        simp [v13RealLinearComp,
          v13RealLinearTwoRowZeroShear_apply_row₁, hArow₁, hsum]
      have hsupportSumOne :
          support.sum
              (fun r => A.val.val.toEquiv probe r.val) = 1 := by
        calc
          support.sum
              (fun r => A.val.val.toEquiv probe r.val) =
            A.val.val.toEquiv probe row₀.val := by
              refine
                Finset.sum_eq_single
                  (s := support)
                  (f := fun r : {row : Fin m // row ∈ rows} =>
                    A.val.val.toEquiv probe r.val)
                  row₀ ?_ ?_
              · intro r _hr hrne
                have hval : r.val ≠ row₀.val := by
                  intro h
                  exact hrne (Subtype.ext h)
                simp [probe, v13RealLinearSingleBit, hval]
              · intro hnot
                exact False.elim (hnot hrow₀)
          _ = 1 := hArow₀
      have htargetBit : probe i₀ = 1 := by
        calc
          probe i₀ =
              support.sum
                (fun r => A.val.val.toEquiv probe r.val) :=
                (A.property probe).symm
          _ = 1 := hsupportSumOne
      have hbad := htarget probe
      rw [hleft, htargetBit] at hbad
      norm_num at hbad
    · have htargetA : row ∈ V13RealLinearTargetRows A.val.val i₀ := by
        rw [v13RealLinear_mem_targetRows_iff]
        intro w
        have h := htarget w
        simpa [v13RealLinearComp,
          v13RealLinearTwoRowZeroShear_apply_of_ne row₀.val row₁.val s
            (A.val.val.toEquiv w) hrow] using h
      have hnot : row ∉ V13RealLinearTargetRows A.val.val i₀ := by
        rw [A.val.property]
        simp
      exact False.elim (hnot htargetA)
  · intro hrow
    simp at hrow

noncomputable def v13RealLinearNoTargetFixedSupportSumTargetShear
    {m : Nat} {rows : Finset (Fin m)} (i₀ : Fin m)
    {support : Finset {row : Fin m // row ∈ rows}}
    (row₀ row₁ : {row : Fin m // row ∈ rows})
    (hrow₀ : row₀ ∈ support) (hrow₁ : row₁ ∈ support)
    (hneq : row₀ ≠ row₁)
    (A : V13RealLinearNoTargetFixedSupportSumTargetMapSet i₀ support)
    (s : V13RealLinearTwoRowZeroAt row₀.val row₁.val) :
    V13RealLinearNoTargetRowsMap m i₀ :=
  ⟨v13RealLinearComp
      (v13RealLinearTwoRowZeroShear row₀.val row₁.val s) A.val.val,
    v13RealLinearNoTargetFixedSupportSumTarget_shear_targetRows_empty
      i₀ row₀ row₁ hrow₀ hrow₁ hneq A s⟩

noncomputable def
    v13RealLinearNoTargetFixedSupportSumTargetMapSetShearEmbedding
    {m : Nat} {rows : Finset (Fin m)} (i₀ : Fin m)
    {support : Finset {row : Fin m // row ∈ rows}}
    (row₀ row₁ : {row : Fin m // row ∈ rows})
    (hrow₀ : row₀ ∈ support) (hrow₁ : row₁ ∈ support)
    (hneq : row₀ ≠ row₁) :
    V13RealLinearNoTargetFixedSupportSumTargetMapSet i₀ support ×
        V13RealLinearTwoRowZeroAt row₀.val row₁.val ↪
      V13RealLinearNoTargetRowsMap m i₀ where
  toFun pair :=
    v13RealLinearNoTargetFixedSupportSumTargetShear
      i₀ row₀ row₁ hrow₀ hrow₁ hneq pair.1 pair.2
  inj' := by
    classical
    intro pair₀ pair₁ hmap
    rcases pair₀ with ⟨A₀, s₀⟩
    rcases pair₁ with ⟨A₁, s₁⟩
    have hB :
        v13RealLinearComp
            (v13RealLinearTwoRowZeroShear row₀.val row₁.val s₀)
            A₀.val.val =
          v13RealLinearComp
            (v13RealLinearTwoRowZeroShear row₀.val row₁.val s₁)
            A₁.val.val :=
      congrArg Subtype.val hmap
    have hneqVal : row₀.val ≠ row₁.val := fun h => hneq (Subtype.ext h)
    have hrowEqOfNe :
        ∀ (row : Fin m), row ≠ row₁.val →
          ∀ w : F2Vec m,
            A₀.val.val.toEquiv w row = A₁.val.val.toEquiv w row := by
      intro row hrow w
      have h := congrFun (congrArg
        (fun A : V13F2LinearEquiv m => A.toEquiv w) hB) row
      simpa [v13RealLinearComp,
        v13RealLinearTwoRowZeroShear_apply_of_ne row₀.val row₁.val s₀
          (A₀.val.val.toEquiv w) hrow,
        v13RealLinearTwoRowZeroShear_apply_of_ne row₀.val row₁.val s₁
          (A₁.val.val.toEquiv w) hrow] using h
    have hrow₁Eq :
        ∀ w : F2Vec m,
          A₀.val.val.toEquiv w row₁.val =
            A₁.val.val.toEquiv w row₁.val := by
      intro w
      have herase :
          (support.erase row₁).sum
              (fun r => A₀.val.val.toEquiv w r.val) =
            (support.erase row₁).sum
              (fun r => A₁.val.val.toEquiv w r.val) := by
        apply Finset.sum_congr rfl
        intro r hr
        have hneSubtype : r ≠ row₁ := (Finset.mem_erase.mp hr).1
        have hneVal : r.val ≠ row₁.val := by
          intro h
          exact hneSubtype (Subtype.ext h)
        exact hrowEqOfNe r.val hneVal w
      have hsum₀ := A₀.property w
      have hsum₁ := A₁.property w
      rw [← Finset.sum_erase_add support
        (fun r => A₀.val.val.toEquiv w r.val) hrow₁] at hsum₀
      rw [← Finset.sum_erase_add support
        (fun r => A₁.val.val.toEquiv w r.val) hrow₁] at hsum₁
      let e₀ := (support.erase row₁).sum
        (fun r => A₀.val.val.toEquiv w r.val)
      let e₁ := (support.erase row₁).sum
        (fun r => A₁.val.val.toEquiv w r.val)
      let x₀ := A₀.val.val.toEquiv w row₁.val
      let x₁ := A₁.val.val.toEquiv w row₁.val
      have he : e₀ = e₁ := by simpa [e₀, e₁] using herase
      have hx₀ : e₀ + x₀ = w i₀ := by simpa [e₀, x₀] using hsum₀
      have hx₁ : e₁ + x₁ = w i₀ := by simpa [e₁, x₁] using hsum₁
      calc
        x₀ = x₀ + e₀ + e₀ := by
          exact (f2_add_right_self x₀ e₀).symm
        _ = (e₀ + x₀) + e₀ := by ring
        _ = w i₀ + e₀ := by rw [hx₀]
        _ = w i₀ + e₁ := by rw [he]
        _ = (e₁ + x₁) + e₁ := by rw [hx₁]
        _ = x₁ + e₁ + e₁ := by ring
        _ = x₁ := by
          exact f2_add_right_self x₁ e₁
    have hAEq : A₀ = A₁ := by
      apply Subtype.ext
      apply Subtype.ext
      apply v13RealLinearEquiv_ext
      intro w
      funext row
      by_cases hrow : row = row₁.val
      · subst row
        exact hrow₁Eq w
      · exact hrowEqOfNe row hrow w
    subst A₁
    have hs : s₀ = s₁ := by
      apply Subtype.ext
      funext row
      by_cases hrow₀val : row = row₀.val
      · subst row
        rw [s₀.property.1, s₁.property.1]
      · by_cases hrow₁val : row = row₁.val
        · subst row
          rw [s₀.property.2, s₁.property.2]
        · let probe : F2Vec m :=
            A₀.val.val.toEquiv.symm (v13RealLinearSingleBit row)
          have h := congrFun (congrArg
            (fun A : V13F2LinearEquiv m => A.toEquiv probe) hB) row₁.val
          have hsum₀ :
              v13RealLinearTwoRowZeroShearSum row₀.val row₁.val s₀
                  (A₀.val.val.toEquiv probe) = s₀.val row := by
            simpa [probe] using
              (v13RealLinearTwoRowZeroShearSum_singleBit
                row₀.val row₁.val s₀ hrow₁val)
          have hsum₁ :
              v13RealLinearTwoRowZeroShearSum row₀.val row₁.val s₁
                  (A₀.val.val.toEquiv probe) = s₁.val row := by
            simpa [probe] using
              (v13RealLinearTwoRowZeroShearSum_singleBit
                row₀.val row₁.val s₁ hrow₁val)
          simpa [v13RealLinearComp,
            v13RealLinearTwoRowZeroShear_apply_row₁,
            hsum₀, hsum₁] using h
    subst s₁
    rfl

theorem
    v13RealLinearNoTargetFixedSupportSumTargetMapSet_card_mul_two_pow_le_noTarget
    {m : Nat} {rows : Finset (Fin m)} (i₀ : Fin m)
    (support : Finset {row : Fin m // row ∈ rows})
    (hsupport : 2 ≤ support.card) :
    Fintype.card
        (V13RealLinearNoTargetFixedSupportSumTargetMapSet i₀ support) *
      2 ^ m ≤
    4 * Fintype.card (V13RealLinearNoTargetRowsMap m i₀) := by
  classical
  have hsupportPos : 0 < support.card := by omega
  rcases Finset.card_pos.mp hsupportPos with ⟨row₀, hrow₀⟩
  let rest := support.erase row₀
  have hrestPos : 0 < rest.card := by
    dsimp [rest]
    rw [Finset.card_erase_of_mem hrow₀]
    omega
  rcases Finset.card_pos.mp hrestPos with ⟨row₁, hrow₁Rest⟩
  have hrow₁ : row₁ ∈ support := (Finset.mem_erase.mp hrow₁Rest).2
  have hneq : row₀ ≠ row₁ := (Finset.mem_erase.mp hrow₁Rest).1.symm
  have hneqVal : row₀.val ≠ row₁.val := fun h => hneq (Subtype.ext h)
  let S :=
    Fintype.card
      (V13RealLinearNoTargetFixedSupportSumTargetMapSet i₀ support)
  let Z := Fintype.card (V13RealLinearTwoRowZeroAt row₀.val row₁.val)
  let N := Fintype.card (V13RealLinearNoTargetRowsMap m i₀)
  have hSZ : S * Z ≤ N := by
    simpa [S, Z, N, Fintype.card_prod] using
      Fintype.card_le_of_embedding
        (v13RealLinearNoTargetFixedSupportSumTargetMapSetShearEmbedding
          i₀ row₀ row₁ hrow₀ hrow₁ hneq)
  have hZ : Z * 4 = 2 ^ m := by
    simpa [Z] using
      v13RealLinearTwoRowZeroAt_card_mul_four row₀.val row₁.val hneqVal
  calc
    S * 2 ^ m = S * (Z * 4) := by rw [hZ]
    _ = 4 * (S * Z) := by ring
    _ ≤ 4 * N := Nat.mul_le_mul_left 4 hSZ

def v13RealLinearInsertRowsEmbedding {m : Nat}
    (rows : Finset (Fin m)) (row : Fin m) :
    {r : Fin m // r ∈ rows} ↪
      {r : Fin m // r ∈ insert row rows} where
  toFun r := ⟨r.1, Finset.mem_insert_of_mem r.2⟩
  inj' := by
    intro r₀ r₁ h
    exact Subtype.ext
      (congrArg
        (fun r : {r : Fin m // r ∈ insert row rows} => r.1) h)

noncomputable def v13RealLinearFreshFullSupport {m : Nat}
    (rows : Finset (Fin m)) (row : Fin m)
    (support : Finset {r : Fin m // r ∈ rows}) :
    Finset {r : Fin m // r ∈ insert row rows} :=
  insert ⟨row, Finset.mem_insert_self row rows⟩
    (support.map (v13RealLinearInsertRowsEmbedding rows row))

theorem v13RealLinearFreshFullSupport_card
    {m : Nat} {rows : Finset (Fin m)} {row : Fin m}
    (hrow : row ∉ rows) (support : Finset {r : Fin m // r ∈ rows}) :
    (v13RealLinearFreshFullSupport rows row support).card =
      support.card + 1 := by
  classical
  let newRow : {r : Fin m // r ∈ insert row rows} :=
    ⟨row, Finset.mem_insert_self row rows⟩
  let emb := v13RealLinearInsertRowsEmbedding rows row
  have hnewNot : newRow ∉ support.map emb := by
    intro hmem
    rcases (Finset.mem_map.mp hmem) with ⟨oldRow, _hold, hEq⟩
    have hval : oldRow.1 = row := by
      simpa [newRow, emb, v13RealLinearInsertRowsEmbedding] using
        congrArg
          (fun r : {r : Fin m // r ∈ insert row rows} => r.1) hEq
    exact hrow (by simpa [hval] using oldRow.2)
  simp [v13RealLinearFreshFullSupport, newRow, emb, hnewNot]

theorem v13RealLinearFreshFullSupport_sum
    {m : Nat} {rows : Finset (Fin m)} {row : Fin m}
    (A : V13F2LinearEquiv m) (hrow : row ∉ rows)
    (support : Finset {r : Fin m // r ∈ rows}) (w : F2Vec m) :
    (v13RealLinearFreshFullSupport rows row support).sum
        (fun r => A.toEquiv w r.1) =
      A.toEquiv w row +
        support.sum (fun r => A.toEquiv w r.1) := by
  classical
  let newRow : {r : Fin m // r ∈ insert row rows} :=
    ⟨row, Finset.mem_insert_self row rows⟩
  let emb := v13RealLinearInsertRowsEmbedding rows row
  have hnewNot : newRow ∉ support.map emb := by
    intro hmem
    rcases (Finset.mem_map.mp hmem) with ⟨oldRow, _hold, hEq⟩
    have hval : oldRow.1 = row := by
      simpa [newRow, emb, v13RealLinearInsertRowsEmbedding] using
        congrArg
          (fun r : {r : Fin m // r ∈ insert row rows} => r.1) hEq
    exact hrow (by simpa [hval] using oldRow.2)
  rw [v13RealLinearFreshFullSupport, Finset.sum_insert hnewNot]
  simp [newRow, emb, v13RealLinearInsertRowsEmbedding]

theorem
    v13RealLinearNoTargetRows_freshRowFunctionalTargetCosetHit_exists_support_sum
    {m : Nat} {i₀ : Fin m} {rows : Finset (Fin m)} {row : Fin m}
    (A : V13RealLinearNoTargetRowsMap m i₀) (hrow : row ∉ rows)
    (hhit :
      V13RealLinearRowFunctionalTargetCosetHit A.val rows i₀ row) :
    ∃ support : Finset {r : Fin m // r ∈ rows},
      0 < support.card ∧
        ∀ w : F2Vec m,
          (v13RealLinearFreshFullSupport rows row support).sum
              (fun r => A.val.toEquiv w r.1) =
            w i₀ := by
  classical
  rcases hhit with ⟨z, hz, htarget⟩
  rcases
      (Submodule.mem_span_range_iff_exists_fun (R := ZMod 2)).1
        (by simpa [V13RealLinearRowsFunctionalSpan] using hz) with
    ⟨coeff, hcoeff⟩
  let support := v13RealLinearRowCombinationSupport coeff
  have hcoeffOne :
      ∀ r : {r : Fin m // r ∈ rows},
        r ∈ support → coeff r = 1 := by
    intro r hr
    exact
      v13_zmod2_eq_one_of_ne_zero _
        ((v13RealLinearRowCombinationSupport_mem coeff r).1
          (by simpa [support] using hr))
  have hcoeffZero :
      ∀ r : {r : Fin m // r ∈ rows},
        r ∉ support → coeff r = 0 := by
    intro r hr
    by_contra hne
    exact hr
      (by
        simpa [support] using
          (v13RealLinearRowCombinationSupport_mem coeff r).2 hne)
  have hz_eval :
      ∀ w : F2Vec m,
        z w = support.sum (fun r => A.val.toEquiv w r.1) := by
    intro w
    have hpoint := LinearMap.congr_fun hcoeff w
    let term : {r : Fin m // r ∈ rows} → ZMod 2 :=
      fun r => coeff r * A.val.toEquiv w r.1
    have hsumSupport :
        (∑ r : {r : Fin m // r ∈ rows},
          (coeff r • v13RealLinearRowFunctional A.val r.1) w) =
          support.sum term := by
      symm
      refine Finset.sum_subset (by intro r _hr; simp) ?_
      intro r _hr hnot
      simp [hcoeffZero r hnot]
    have hsupportTerm :
        support.sum (fun r => A.val.toEquiv w r.1) =
          support.sum term := by
      apply Finset.sum_congr rfl
      intro r hr
      simp [term, hcoeffOne r hr]
    calc
      z w =
          (∑ r : {r : Fin m // r ∈ rows},
            (coeff r • v13RealLinearRowFunctional A.val r.1) w) := by
            simpa using hpoint.symm
      _ = support.sum term := hsumSupport
      _ = support.sum (fun r => A.val.toEquiv w r.1) := hsupportTerm.symm
  have hsupportPos : 0 < support.card := by
    by_contra hnot
    have hsupportEmpty : support = ∅ := by
      exact Finset.card_eq_zero.mp (Nat.eq_zero_of_not_pos hnot)
    have hzZero : z = 0 := by
      apply LinearMap.ext
      intro w
      rw [hz_eval w, hsupportEmpty]
      simp
    have htargetRow :
        row ∈ V13RealLinearTargetRows A.val i₀ := by
      rw [v13RealLinear_mem_targetRows_iff]
      intro w
      have hpoint := LinearMap.congr_fun htarget w
      simpa [v13RealLinearTargetFunctional, v13RealLinearRowFunctional,
        hzZero] using hpoint.symm
    have hrowNotTarget :
        row ∉ V13RealLinearTargetRows A.val i₀ := by
      rw [A.property]
      simp
    exact hrowNotTarget htargetRow
  refine ⟨support, hsupportPos, ?_⟩
  intro w
  have hpoint := LinearMap.congr_fun htarget w
  calc
    (v13RealLinearFreshFullSupport rows row support).sum
        (fun r => A.val.toEquiv w r.1) =
        A.val.toEquiv w row +
          support.sum (fun r => A.val.toEquiv w r.1) :=
      v13RealLinearFreshFullSupport_sum A.val hrow support w
    _ = A.val.toEquiv w row + z w := by rw [hz_eval w]
    _ = w i₀ := by
      simpa [v13RealLinearTargetFunctional, v13RealLinearRowFunctional]
        using hpoint.symm

abbrev V13RealLinearNoTargetFreshRowCosetHitSupportSigma
    {m : Nat} (i₀ : Fin m) (rows : Finset (Fin m)) (row : Fin m) :=
  Σ support :
      {support : Finset {r : Fin m // r ∈ rows} //
        0 < support.card},
    V13RealLinearNoTargetFixedSupportSumTargetMapSet i₀
      (v13RealLinearFreshFullSupport rows row support.val)

noncomputable instance {m : Nat} (i₀ : Fin m)
    (rows : Finset (Fin m)) (row : Fin m) :
    Fintype
      (V13RealLinearNoTargetFreshRowCosetHitSupportSigma
        i₀ rows row) := by
  classical
  unfold V13RealLinearNoTargetFreshRowCosetHitSupportSigma
  infer_instance

noncomputable def
    v13RealLinearNoTargetFreshRowCosetHitEmbeddingSupportSigma
    {m : Nat} (i₀ : Fin m) (rows : Finset (Fin m)) (row : Fin m)
    (hrow : row ∉ rows) :
    {A : V13RealLinearNoTargetRowsMap m i₀ //
      V13RealLinearRowFunctionalTargetCosetHit A.val rows i₀ row} ↪
      V13RealLinearNoTargetFreshRowCosetHitSupportSigma
        i₀ rows row where
  toFun A := by
    classical
    let ex :=
      v13RealLinearNoTargetRows_freshRowFunctionalTargetCosetHit_exists_support_sum
        A.val hrow A.property
    let support := Classical.choose ex
    let spec := Classical.choose_spec ex
    exact ⟨⟨support, spec.1⟩, ⟨A.val, spec.2⟩⟩
  inj' := by
    intro A₀ A₁ h
    apply Subtype.ext
    exact
      congrArg
        (fun data :
          V13RealLinearNoTargetFreshRowCosetHitSupportSigma
            i₀ rows row =>
          data.2.val)
        h

noncomputable instance {m : Nat} (i₀ : Fin m)
    (rows : Finset (Fin m)) (row : Fin m) :
    Fintype
      {A : V13RealLinearNoTargetRowsMap m i₀ //
        V13RealLinearRowFunctionalTargetCosetHit A.val rows i₀ row} := by
  classical
  infer_instance

theorem
    v13RealLinearNoTargetFreshRowCosetHitSupportSigma_card_mul_two_pow_le
    {m : Nat} (i₀ : Fin m) (rows : Finset (Fin m)) (row : Fin m)
    (hrow : row ∉ rows) :
    Fintype.card
        (V13RealLinearNoTargetFreshRowCosetHitSupportSigma i₀ rows row) *
      2 ^ m ≤
    4 * 2 ^ rows.card *
      Fintype.card (V13RealLinearNoTargetRowsMap m i₀) := by
  classical
  let N := Fintype.card (V13RealLinearNoTargetRowsMap m i₀)
  let M := 2 ^ m
  have hSupportLe :
      Fintype.card
          {support : Finset {r : Fin m // r ∈ rows} //
            0 < support.card} ≤
        2 ^ rows.card := by
    calc
      Fintype.card
          {support : Finset {r : Fin m // r ∈ rows} //
            0 < support.card} ≤
          Fintype.card (Finset {r : Fin m // r ∈ rows}) := by
        exact Fintype.card_subtype_le
          (fun support : Finset {r : Fin m // r ∈ rows} =>
            0 < support.card)
      _ = 2 ^ Fintype.card {r : Fin m // r ∈ rows} :=
        Fintype.card_finset
      _ = 2 ^ rows.card := by simp
  have hterm :
      ∀ support :
          {support : Finset {r : Fin m // r ∈ rows} //
            0 < support.card},
        Fintype.card
            (V13RealLinearNoTargetFixedSupportSumTargetMapSet i₀
              (v13RealLinearFreshFullSupport rows row support.val)) *
          M ≤ 4 * N := by
    intro support
    have htwo :
        2 ≤ (v13RealLinearFreshFullSupport rows row support.val).card := by
      rw [v13RealLinearFreshFullSupport_card hrow support.val]
      omega
    simpa [M, N] using
      v13RealLinearNoTargetFixedSupportSumTargetMapSet_card_mul_two_pow_le_noTarget
        i₀ (v13RealLinearFreshFullSupport rows row support.val) htwo
  change
    Fintype.card
        ((support :
            {support : Finset {r : Fin m // r ∈ rows} //
              0 < support.card}) ×
          V13RealLinearNoTargetFixedSupportSumTargetMapSet i₀
            (v13RealLinearFreshFullSupport rows row support.val)) *
      M ≤ 4 * 2 ^ rows.card * N
  have hcardSigma :
      Fintype.card
          ((support :
              {support : Finset {r : Fin m // r ∈ rows} //
                0 < support.card}) ×
            V13RealLinearNoTargetFixedSupportSumTargetMapSet i₀
              (v13RealLinearFreshFullSupport rows row support.val)) =
        ∑ support :
            {support : Finset {r : Fin m // r ∈ rows} //
              0 < support.card},
          Fintype.card
            (V13RealLinearNoTargetFixedSupportSumTargetMapSet i₀
              (v13RealLinearFreshFullSupport rows row support.val)) := by
    let sigmaFinset :
        Finset
          ((support :
              {support : Finset {r : Fin m // r ∈ rows} //
                0 < support.card}) ×
            V13RealLinearNoTargetFixedSupportSumTargetMapSet i₀
              (v13RealLinearFreshFullSupport rows row support.val)) :=
      Finset.univ.sigma
        (fun support :
            {support : Finset {r : Fin m // r ∈ rows} //
              0 < support.card} =>
          (Finset.univ :
            Finset
              (V13RealLinearNoTargetFixedSupportSumTargetMapSet i₀
                (v13RealLinearFreshFullSupport rows row support.val))))
    have hcard :
        Fintype.card
            ((support :
                {support : Finset {r : Fin m // r ∈ rows} //
                  0 < support.card}) ×
              V13RealLinearNoTargetFixedSupportSumTargetMapSet i₀
                (v13RealLinearFreshFullSupport rows row support.val)) =
          sigmaFinset.card := by
      have hsigUniv : sigmaFinset = Finset.univ := by
        dsimp [sigmaFinset]
        exact Finset.univ_sigma_univ
      rw [← Finset.card_univ, ← hsigUniv]
    have hsigma :
        sigmaFinset.card =
          ∑ support :
              {support : Finset {r : Fin m // r ∈ rows} //
                0 < support.card},
            Fintype.card
              (V13RealLinearNoTargetFixedSupportSumTargetMapSet i₀
                (v13RealLinearFreshFullSupport rows row support.val)) := by
      simp [sigmaFinset]
    exact hcard.trans hsigma
  rw [hcardSigma]
  rw [Finset.sum_mul]
  calc
    (∑ support :
        {support : Finset {r : Fin m // r ∈ rows} //
          0 < support.card},
        Fintype.card
            (V13RealLinearNoTargetFixedSupportSumTargetMapSet i₀
              (v13RealLinearFreshFullSupport rows row support.val)) *
          M) ≤
        ∑ _support :
            {support : Finset {r : Fin m // r ∈ rows} //
              0 < support.card}, 4 * N := by
          apply Finset.sum_le_sum
          intro support _hsupport
          exact hterm support
    _ =
        Fintype.card
          {support : Finset {r : Fin m // r ∈ rows} //
            0 < support.card} *
          (4 * N) := by
      rw [Finset.sum_const]
      simp
    _ ≤ 2 ^ rows.card * (4 * N) := by
      exact Nat.mul_le_mul_right (4 * N) hSupportLe
    _ = 4 * 2 ^ rows.card * N := by ring

theorem
    v13RealLinearNoTargetFreshRowCosetHitMapSet_card_mul_two_pow_le
    {m : Nat} (i₀ : Fin m) (rows : Finset (Fin m)) (row : Fin m)
    (hrow : row ∉ rows) :
    Fintype.card
        {A : V13RealLinearNoTargetRowsMap m i₀ //
          V13RealLinearRowFunctionalTargetCosetHit A.val rows i₀ row} *
      2 ^ m ≤
    4 * 2 ^ rows.card *
      Fintype.card (V13RealLinearNoTargetRowsMap m i₀) := by
  classical
  let S :=
    {A : V13RealLinearNoTargetRowsMap m i₀ //
      V13RealLinearRowFunctionalTargetCosetHit A.val rows i₀ row}
  let W := V13RealLinearNoTargetFreshRowCosetHitSupportSigma i₀ rows row
  let N := Fintype.card (V13RealLinearNoTargetRowsMap m i₀)
  let M := 2 ^ m
  have hS : Fintype.card S ≤ Fintype.card W :=
    Fintype.card_le_of_embedding
      (v13RealLinearNoTargetFreshRowCosetHitEmbeddingSupportSigma
        i₀ rows row hrow)
  have hW : Fintype.card W * M ≤ 4 * 2 ^ rows.card * N := by
    simpa [W, M, N] using
      v13RealLinearNoTargetFreshRowCosetHitSupportSigma_card_mul_two_pow_le
        i₀ rows row hrow
  calc
    Fintype.card S * M ≤ Fintype.card W * M :=
      Nat.mul_le_mul_right M hS
    _ ≤ 4 * 2 ^ rows.card * N := hW

abbrev V13RealLinearNoTargetSupportSumWitnessSigma
    {m j : Nat} (i₀ : Fin m) (rows : V13RealLinearBudgetedRowset m j) :=
  Σ support :
      {support : Finset {row : Fin m // row ∈ rows.1} //
        2 ≤ support.card},
    V13RealLinearNoTargetFixedSupportSumTargetMapSet i₀ support.val

noncomputable instance {m j : Nat} (i₀ : Fin m)
    (rows : V13RealLinearBudgetedRowset m j) :
    Fintype (V13RealLinearNoTargetSupportSumWitnessSigma i₀ rows) := by
  classical
  unfold V13RealLinearNoTargetSupportSumWitnessSigma
  infer_instance

noncomputable def
    v13RealLinearNoTargetBudgetedRowsetGeneratingMapSetEmbeddingSupportSumSigma
    {m j : Nat} (i₀ : Fin m) (rows : V13RealLinearBudgetedRowset m j) :
    V13RealLinearNoTargetBudgetedRowsetGeneratingMapSet i₀ rows ↪
      V13RealLinearNoTargetSupportSumWitnessSigma i₀ rows where
  toFun A := by
    classical
    let ex :=
      v13RealLinearNoTargetBudgetedRowsetGeneratingMapSet_exists_support_sum_target
        A
    let support := Classical.choose ex
    let spec := Classical.choose_spec ex
    exact ⟨⟨support, spec.1⟩, ⟨A.val, spec.2.2⟩⟩
  inj' := by
    intro A₀ A₁ h
    apply Subtype.ext
    exact
      congrArg
        (fun data :
          V13RealLinearNoTargetSupportSumWitnessSigma i₀ rows =>
          data.2.val)
        h

theorem
    v13RealLinearNoTargetSupportSumWitnessSigma_card_mul_two_pow_le
    {m j : Nat} (i₀ : Fin m) (rows : V13RealLinearBudgetedRowset m j) :
    Fintype.card
        (V13RealLinearNoTargetSupportSumWitnessSigma i₀ rows) *
      2 ^ m ≤
  4 * 2 ^ j * Fintype.card (V13RealLinearNoTargetRowsMap m i₀) := by
  classical
  let N := Fintype.card (V13RealLinearNoTargetRowsMap m i₀)
  let M := 2 ^ m
  have hRowLe : Fintype.card {row : Fin m // row ∈ rows.1} ≤ j := by
    simpa using rows.2
  have hSupportLe :
      Fintype.card
          {support : Finset {row : Fin m // row ∈ rows.1} //
            2 ≤ support.card} ≤
        2 ^ j := by
    calc
      Fintype.card
          {support : Finset {row : Fin m // row ∈ rows.1} //
            2 ≤ support.card} ≤
          Fintype.card (Finset {row : Fin m // row ∈ rows.1}) := by
        exact Fintype.card_subtype_le
          (fun support :
            Finset {row : Fin m // row ∈ rows.1} =>
              2 ≤ support.card)
      _ = 2 ^ Fintype.card {row : Fin m // row ∈ rows.1} :=
        Fintype.card_finset
      _ ≤ 2 ^ j := by
        exact Nat.pow_le_pow_right (by norm_num : 0 < 2) hRowLe
  have hterm :
      ∀ support :
          {support : Finset {row : Fin m // row ∈ rows.1} //
            2 ≤ support.card},
        Fintype.card
            (V13RealLinearNoTargetFixedSupportSumTargetMapSet
              i₀ support.val) *
          M ≤ 4 * N := by
    intro support
    simpa [M, N] using
      v13RealLinearNoTargetFixedSupportSumTargetMapSet_card_mul_two_pow_le_noTarget
        i₀ support.val support.property
  change
    Fintype.card
        ((support :
            {support : Finset {row : Fin m // row ∈ rows.1} //
              2 ≤ support.card}) ×
          V13RealLinearNoTargetFixedSupportSumTargetMapSet i₀ support.val) *
      M ≤ 4 * 2 ^ j * N
  have hcardSigma :
      Fintype.card
          ((support :
              {support : Finset {row : Fin m // row ∈ rows.1} //
                2 ≤ support.card}) ×
            V13RealLinearNoTargetFixedSupportSumTargetMapSet i₀ support.val) =
        ∑ support :
            {support : Finset {row : Fin m // row ∈ rows.1} //
              2 ≤ support.card},
          Fintype.card
            (V13RealLinearNoTargetFixedSupportSumTargetMapSet
              i₀ support.val) := by
    let sigmaFinset :
        Finset
          ((support :
              {support : Finset {row : Fin m // row ∈ rows.1} //
                2 ≤ support.card}) ×
            V13RealLinearNoTargetFixedSupportSumTargetMapSet
              i₀ support.val) :=
      Finset.univ.sigma
        (fun support :
            {support : Finset {row : Fin m // row ∈ rows.1} //
              2 ≤ support.card} =>
          (Finset.univ :
            Finset
              (V13RealLinearNoTargetFixedSupportSumTargetMapSet
                i₀ support.val)))
    have hcard :
        Fintype.card
            ((support :
                {support : Finset {row : Fin m // row ∈ rows.1} //
                  2 ≤ support.card}) ×
              V13RealLinearNoTargetFixedSupportSumTargetMapSet
                i₀ support.val) =
          sigmaFinset.card := by
      have hsigUniv : sigmaFinset = Finset.univ := by
        dsimp [sigmaFinset]
        exact Finset.univ_sigma_univ
      rw [← Finset.card_univ, ← hsigUniv]
    have hsigma :
        sigmaFinset.card =
          ∑ support :
              {support : Finset {row : Fin m // row ∈ rows.1} //
                2 ≤ support.card},
            Fintype.card
              (V13RealLinearNoTargetFixedSupportSumTargetMapSet
                i₀ support.val) := by
      simp [sigmaFinset]
    exact hcard.trans hsigma
  rw [hcardSigma]
  rw [Finset.sum_mul]
  calc
    (∑ support :
        {support : Finset {row : Fin m // row ∈ rows.1} //
          2 ≤ support.card},
        Fintype.card
            (V13RealLinearNoTargetFixedSupportSumTargetMapSet
              i₀ support.val) *
          M) ≤
        ∑ _support :
            {support : Finset {row : Fin m // row ∈ rows.1} //
              2 ≤ support.card}, 4 * N := by
          apply Finset.sum_le_sum
          intro support _hsupport
          exact hterm support
    _ =
        Fintype.card
          {support : Finset {row : Fin m // row ∈ rows.1} //
            2 ≤ support.card} *
          (4 * N) := by
      rw [Finset.sum_const]
      simp
    _ ≤ 2 ^ j * (4 * N) := by
      exact Nat.mul_le_mul_right (4 * N) hSupportLe
    _ = 4 * 2 ^ j * N := by ring

theorem
    V13RealLinearNoTargetBudgetedRowsetGenerationCountingBound_allBudget
    (m j : Nat) :
    V13RealLinearNoTargetBudgetedRowsetGenerationCountingBound m j := by
  intro i₀ rows
  let G := V13RealLinearNoTargetBudgetedRowsetGeneratingMapSet i₀ rows
  let W := V13RealLinearNoTargetSupportSumWitnessSigma i₀ rows
  let N := Fintype.card (V13RealLinearNoTargetRowsMap m i₀)
  let M := 2 ^ m
  have hG : Fintype.card G ≤ Fintype.card W :=
    Fintype.card_le_of_embedding
      (v13RealLinearNoTargetBudgetedRowsetGeneratingMapSetEmbeddingSupportSumSigma
        i₀ rows)
  have hW : Fintype.card W * M ≤ 4 * 2 ^ j * N := by
    simpa [W, M, N] using
      v13RealLinearNoTargetSupportSumWitnessSigma_card_mul_two_pow_le
        i₀ rows
  calc
    M * Fintype.card G = Fintype.card G * M := by ring
    _ ≤ Fintype.card W * M := Nat.mul_le_mul_right M hG
    _ ≤ 4 * 2 ^ j * N := hW

theorem
    v13RealLinearNoTargetExistingRowCosetHitMapSet_card_mul_two_pow_le
    {m : Nat} (i₀ : Fin m) (rows : Finset (Fin m)) (row : Fin m)
    (hrow : row ∈ rows) :
    Fintype.card
        {A : V13RealLinearNoTargetRowsMap m i₀ //
          V13RealLinearRowFunctionalTargetCosetHit A.val rows i₀ row} *
      2 ^ m ≤
    4 * 2 ^ rows.card *
      Fintype.card (V13RealLinearNoTargetRowsMap m i₀) := by
  classical
  let S :=
    {A : V13RealLinearNoTargetRowsMap m i₀ //
      V13RealLinearRowFunctionalTargetCosetHit A.val rows i₀ row}
  let budgetRows : V13RealLinearBudgetedRowset m rows.card :=
    ⟨rows, le_rfl⟩
  let G := V13RealLinearNoTargetBudgetedRowsetGeneratingMapSet i₀ budgetRows
  let N := Fintype.card (V13RealLinearNoTargetRowsMap m i₀)
  let M := 2 ^ m
  have hS : Fintype.card S ≤ Fintype.card G := by
    dsimp [S, G, budgetRows,
      V13RealLinearNoTargetBudgetedRowsetGeneratingMapSet]
    exact
      Fintype.card_le_of_embedding
        { toFun := fun A =>
            ⟨A.val,
              v13RealLinear_rowsGenerateTarget_of_rowFunctionalTargetCosetHit_of_mem
                A.val.val i₀ row hrow A.property⟩
          inj' := by
            intro A₀ A₁ h
            apply Subtype.ext
            exact
              congrArg
                (fun A :
                  {A : V13RealLinearNoTargetRowsMap m i₀ //
                    V13RealLinearRowsGenerateTarget A.val rows i₀} =>
                  A.val)
                h }
  have hG :
      M * Fintype.card G ≤ 4 * 2 ^ rows.card * N := by
    simpa [M, G, N, budgetRows] using
      (V13RealLinearNoTargetBudgetedRowsetGenerationCountingBound_allBudget
        m rows.card i₀ budgetRows)
  calc
    Fintype.card S * M = M * Fintype.card S := by ring
    _ ≤ M * Fintype.card G := Nat.mul_le_mul_left M hS
    _ ≤ 4 * 2 ^ rows.card * N := hG

theorem
    v13RealLinearNoTargetFixedRowsetCosetHitMapSet_card_mul_two_pow_le
    {m : Nat} (i₀ : Fin m) (rows : Finset (Fin m)) (row : Fin m) :
    Fintype.card
        {A : V13RealLinearNoTargetRowsMap m i₀ //
          V13RealLinearRowFunctionalTargetCosetHit A.val rows i₀ row} *
      2 ^ m ≤
    4 * 2 ^ rows.card *
      Fintype.card (V13RealLinearNoTargetRowsMap m i₀) := by
  classical
  by_cases hrow : row ∈ rows
  · exact
      v13RealLinearNoTargetExistingRowCosetHitMapSet_card_mul_two_pow_le
        i₀ rows row hrow
  · exact
      v13RealLinearNoTargetFreshRowCosetHitMapSet_card_mul_two_pow_le
        i₀ rows row hrow

/-- Worlds whose sequential no-target trace has a coset hit at a fixed step
and whose realized prefix rowset and next row are the specified fixed data.
This is the world-space fiber of the fixed-prefix map count above. -/
abbrev V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixWorldSet
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (rows : Finset (Fin m)) (row : Fin m) :=
  {omega :
      V13RealLinearAdaptiveQRowWorld m
        (V13RealLinearNoTargetRowsMap m i₀) //
    V13RealLinearAdaptiveQRowTraceFirstCosetHit
      (v13RealLinearNoTargetRowsSequentialQRowExperiment i₀ observer)
      i₀
      (v13RealLinearNoTargetRowsSequentialQRowTrace i₀ observer)
      t omega ∧
    v13RealLinearRowTracePrefixRows
      (v13RealLinearNoTargetRowsSequentialQRowTrace i₀ observer omega)
      (t : Nat) = rows ∧
    ∃ h : (t : Nat) <
        (v13RealLinearNoTargetRowsSequentialQRowTrace i₀ observer omega).length,
      (v13RealLinearNoTargetRowsSequentialQRowTrace i₀ observer omega).get
        ⟨(t : Nat), h⟩ = row}

noncomputable instance
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (rows : Finset (Fin m)) (row : Fin m) :
    Fintype
      (V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixWorldSet
        i₀ observer t rows row) := by
  classical
  unfold V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixWorldSet
  infer_instance

noncomputable def
    v13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixWorldSetToMapTimesVector
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (rows : Finset (Fin m)) (row : Fin m) :
    V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixWorldSet
        i₀ observer t rows row ↪
      ({A : V13RealLinearNoTargetRowsMap m i₀ //
          V13RealLinearRowFunctionalTargetCosetHit A.val rows i₀ row} ×
        F2Vec m) where
  toFun omega := by
    classical
    let trace :=
      v13RealLinearNoTargetRowsSequentialQRowTrace i₀ observer omega.val
    have hcoset :
        V13RealLinearRowFunctionalTargetCosetHit omega.val.1.val
          rows i₀ row := by
      rcases omega.property with ⟨hfirst, hrows, hrow⟩
      rcases hfirst.2 with ⟨hhitIndex, hhit⟩
      rcases hrow with ⟨hrowIndex, hget⟩
      have hidx :
          (⟨(t : Nat), hhitIndex⟩ : Fin trace.length) =
            ⟨(t : Nat), hrowIndex⟩ := by
        apply Fin.ext
        rfl
      have hhitRows :
          V13RealLinearRowFunctionalTargetCosetHit
            ((v13RealLinearNoTargetRowsSequentialQRowExperiment
                i₀ observer).sampleA omega.val.1)
            rows i₀ (trace.get ⟨(t : Nat), hhitIndex⟩) := by
        simpa [trace, hrows] using hhit
      have hgetHit : trace.get ⟨(t : Nat), hhitIndex⟩ = row := by
        simpa [trace, hidx] using hget
      rw [hgetHit] at hhitRows
      simpa [v13RealLinearNoTargetRowsSequentialQRowExperiment,
        v13RealLinearNoTargetRowsCausalQRowExperiment,
        v13RealLinearNoTargetRowsQRowExperiment] using hhitRows
    exact (⟨omega.val.1, hcoset⟩, omega.val.2)
  inj' := by
    intro omega₀ omega₁ h
    apply Subtype.ext
    apply Prod.ext
    · exact
        congrArg
          (fun z :
            ({A : V13RealLinearNoTargetRowsMap m i₀ //
                V13RealLinearRowFunctionalTargetCosetHit A.val rows i₀ row} ×
              F2Vec m) => z.1.val)
          h
    · exact
        congrArg
          (fun z :
            ({A : V13RealLinearNoTargetRowsMap m i₀ //
                V13RealLinearRowFunctionalTargetCosetHit A.val rows i₀ row} ×
              F2Vec m) => z.2)
          h

theorem
    v13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixWorldSet_card_mul_two_pow_le_rows
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (rows : Finset (Fin m)) (row : Fin m) :
    Fintype.card
        (V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixWorldSet
          i₀ observer t rows row) *
      2 ^ m ≤
    4 * 2 ^ rows.card *
      Fintype.card
        (V13RealLinearAdaptiveQRowWorld m
          (V13RealLinearNoTargetRowsMap m i₀)) := by
  classical
  let S :=
    {A : V13RealLinearNoTargetRowsMap m i₀ //
      V13RealLinearRowFunctionalTargetCosetHit A.val rows i₀ row}
  let W :=
    V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixWorldSet
      i₀ observer t rows row
  let N := Fintype.card (V13RealLinearNoTargetRowsMap m i₀)
  let M := 2 ^ m
  have hW :
      Fintype.card W ≤ Fintype.card (S × F2Vec m) :=
    Fintype.card_le_of_embedding
      (v13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixWorldSetToMapTimesVector
        i₀ observer t rows row)
  have hWprod : Fintype.card W ≤ Fintype.card S * M := by
    simpa [S, M, Fintype.card_prod, v13RealLinear_f2vec_card] using hW
  have hfixed :
      Fintype.card S * M ≤ 4 * 2 ^ rows.card * N := by
    simpa [S, M, N] using
      v13RealLinearNoTargetFixedRowsetCosetHitMapSet_card_mul_two_pow_le
        i₀ rows row
  have hmul :
      Fintype.card W * M ≤ (4 * 2 ^ rows.card * N) * M := by
    exact
      (Nat.mul_le_mul_right M hWprod).trans
        (Nat.mul_le_mul_right M hfixed)
  have hworld :
      Fintype.card
          (V13RealLinearAdaptiveQRowWorld m
            (V13RealLinearNoTargetRowsMap m i₀)) =
        N * M := by
    dsimp [V13RealLinearAdaptiveQRowWorld, N, M]
    rw [Fintype.card_prod, v13RealLinear_f2vec_card]
  simpa [W, M, hworld, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
    hmul

theorem
    v13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixWorldSet_card_mul_two_pow_le_step
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (rows : Finset (Fin m)) (row : Fin m) :
    Fintype.card
        (V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixWorldSet
          i₀ observer t rows row) *
      2 ^ m ≤
    4 * 2 ^ (t : Nat) *
      Fintype.card
        (V13RealLinearAdaptiveQRowWorld m
          (V13RealLinearNoTargetRowsMap m i₀)) := by
  classical
  let W :=
    V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixWorldSet
      i₀ observer t rows row
  by_cases hnonempty : Nonempty W
  · rcases hnonempty with ⟨omega⟩
    have hrowsLe : rows.card ≤ (t : Nat) := by
      let trace :=
        v13RealLinearNoTargetRowsSequentialQRowTrace i₀ observer omega.val
      have hprefix :
          (v13RealLinearRowTracePrefixRows trace (t : Nat)).card ≤
            (t : Nat) :=
        v13RealLinearRowTracePrefixRows_card_le trace (t : Nat)
      exact omega.property.2.1 ▸ hprefix
    have hbase :=
      v13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixWorldSet_card_mul_two_pow_le_rows
        i₀ observer t rows row
    have hpow : 2 ^ rows.card ≤ 2 ^ (t : Nat) :=
      Nat.pow_le_pow_right (by norm_num : 0 < 2) hrowsLe
    have hmono :
        4 * 2 ^ rows.card *
            Fintype.card
              (V13RealLinearAdaptiveQRowWorld m
                (V13RealLinearNoTargetRowsMap m i₀)) ≤
          4 * 2 ^ (t : Nat) *
            Fintype.card
              (V13RealLinearAdaptiveQRowWorld m
                (V13RealLinearNoTargetRowsMap m i₀)) := by
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 4 hpow)
    exact hbase.trans hmono
  · have hcard : Fintype.card W = 0 := by
      rw [Fintype.card_eq_zero_iff]
      exact ⟨fun omega => hnonempty ⟨omega⟩⟩
    simp [W, hcard]

/-- A fixed-prefix trace-hit world fiber refined by the row transcript observed
on the realized prefix rowset. -/
abbrev
    V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixTranscriptWorldSet
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (rows : Finset (Fin m)) (row : Fin m)
    (transcript : V13RealLinearRowsTranscriptSpace m rows) :=
  {omega :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixWorldSet
        i₀ observer t rows row //
    v13RealLinearRowsTranscript rows
        (v13RealLinearPublicInput
          ({ x := omega.val.2, A := omega.val.1.val } :
            V13RealLinearWorld m)) =
      transcript}

noncomputable instance
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (rows : Finset (Fin m)) (row : Fin m)
    (transcript : V13RealLinearRowsTranscriptSpace m rows) :
    Fintype
      (V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixTranscriptWorldSet
        i₀ observer t rows row transcript) := by
  classical
  unfold
    V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixTranscriptWorldSet
  infer_instance

noncomputable def
    v13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixTranscriptWorldSetToMapTimesUnreadAssignment
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (rows : Finset (Fin m)) (row : Fin m)
    (transcript : V13RealLinearRowsTranscriptSpace m rows) :
    V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixTranscriptWorldSet
        i₀ observer t rows row transcript ↪
      ({A : V13RealLinearNoTargetRowsMap m i₀ //
          V13RealLinearRowFunctionalTargetCosetHit A.val rows i₀ row} ×
        V13RealLinearRowsUnreadAssignment m rows) where
  toFun omega := by
    classical
    let mapVector :=
      v13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixWorldSetToMapTimesVector
        i₀ observer t rows row omega.val
    exact
      (mapVector.1,
        fun unread => omega.val.val.1.val.toEquiv omega.val.val.2 unread.1)
  inj' := by
    classical
    intro omega₀ omega₁ h
    apply Subtype.ext
    apply Subtype.ext
    let mapVector₀ :=
      v13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixWorldSetToMapTimesVector
        i₀ observer t rows row omega₀.val
    let mapVector₁ :=
      v13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixWorldSetToMapTimesVector
        i₀ observer t rows row omega₁.val
    have hmap :
        mapVector₀.1 = mapVector₁.1 := by
      simpa [mapVector₀, mapVector₁] using congrArg Prod.fst h
    have hA : omega₀.val.val.1 = omega₁.val.val.1 := by
      exact congrArg Subtype.val hmap
    apply Prod.ext
    · exact hA
    · apply omega₀.val.val.1.val.toEquiv.injective
      funext r
      by_cases hr : r ∈ rows
      · have htranscript :
            v13RealLinearRowsTranscript rows
                (v13RealLinearPublicInput
                  ({ x := omega₀.val.val.2, A := omega₀.val.val.1.val } :
                    V13RealLinearWorld m)) =
              v13RealLinearRowsTranscript rows
                (v13RealLinearPublicInput
                  ({ x := omega₁.val.val.2, A := omega₁.val.val.1.val } :
                    V13RealLinearWorld m)) :=
          omega₀.property.trans omega₁.property.symm
        have hview := congrFun htranscript ⟨r, hr⟩
        have hbit :
            omega₀.val.val.1.val.toEquiv omega₀.val.val.2 r =
              omega₁.val.val.1.val.toEquiv omega₁.val.val.2 r := by
          simpa [v13RealLinearRowsTranscript, v13RealLinearRowView,
            v13RealLinearPublicInput] using congrArg Prod.snd hview
        simpa [hA] using hbit
      · have hassign :
            (fun unread : {row : Fin m // row ∉ rows} =>
                omega₀.val.val.1.val.toEquiv omega₀.val.val.2 unread.1)
              =
            (fun unread : {row : Fin m // row ∉ rows} =>
                omega₁.val.val.1.val.toEquiv omega₁.val.val.2 unread.1) := by
          simpa [mapVector₀, mapVector₁] using congrArg Prod.snd h
        have hbit := congrFun hassign ⟨r, hr⟩
        simpa [hA] using hbit

theorem
    v13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixTranscriptWorldSet_card_mul_two_pow_le_world
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (rows : Finset (Fin m)) (row : Fin m)
    (transcript : V13RealLinearRowsTranscriptSpace m rows) :
    Fintype.card
        (V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixTranscriptWorldSet
          i₀ observer t rows row transcript) *
      2 ^ m ≤
    4 *
      Fintype.card
        (V13RealLinearAdaptiveQRowWorld m
          (V13RealLinearNoTargetRowsMap m i₀)) := by
  classical
  let Cell :=
    V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixTranscriptWorldSet
      i₀ observer t rows row transcript
  let S :=
    {A : V13RealLinearNoTargetRowsMap m i₀ //
      V13RealLinearRowFunctionalTargetCosetHit A.val rows i₀ row}
  let U := V13RealLinearRowsUnreadAssignment m rows
  let N := Fintype.card (V13RealLinearNoTargetRowsMap m i₀)
  let M := 2 ^ m
  let R := 2 ^ rows.card
  let Ucard := 2 ^ (m - rows.card)
  have hcell :
      Fintype.card Cell ≤ Fintype.card (S × U) :=
    Fintype.card_le_of_embedding
      (v13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixTranscriptWorldSetToMapTimesUnreadAssignment
        i₀ observer t rows row transcript)
  have hcellProd :
      Fintype.card Cell ≤ Fintype.card S * Ucard := by
    simpa [Cell, S, U, Ucard, Fintype.card_prod,
      v13RealLinearRowsUnreadAssignment_card rows] using hcell
  have hmap :
      Fintype.card S * M ≤ 4 * R * N := by
    simpa [S, M, R, N] using
      v13RealLinearNoTargetFixedRowsetCosetHitMapSet_card_mul_two_pow_le
        i₀ rows row
  have hrowsLe : rows.card ≤ m := by
    have h := Finset.card_le_univ rows
    simpa using h
  have hpowMul : R * Ucard = M := by
    dsimp [R, Ucard, M]
    rw [← pow_add]
    rw [Nat.add_sub_of_le hrowsLe]
  have hworld :
      Fintype.card
          (V13RealLinearAdaptiveQRowWorld m
            (V13RealLinearNoTargetRowsMap m i₀)) =
        N * M := by
    dsimp [V13RealLinearAdaptiveQRowWorld, N, M]
    rw [Fintype.card_prod, v13RealLinear_f2vec_card]
  calc
    Fintype.card Cell * M ≤ (Fintype.card S * Ucard) * M := by
      exact Nat.mul_le_mul_right M hcellProd
    _ = (Fintype.card S * M) * Ucard := by ring
    _ ≤ (4 * R * N) * Ucard := by
      exact Nat.mul_le_mul_right Ucard hmap
    _ = 4 * N * (R * Ucard) := by ring
    _ = 4 * N * M := by rw [hpowMul]
    _ = 4 *
        Fintype.card
          (V13RealLinearAdaptiveQRowWorld m
            (V13RealLinearNoTargetRowsMap m i₀)) := by
      rw [hworld]
      ring

/-- Fixed-map transcript-cylinder index for the no-target first-hit surface.
It records the sampled no-target map, the realized prefix rowset, the chosen
hit row, a proof that this row lies in the target coset of the prefix span, and
the public row transcript on the prefix rowset. -/
structure
    V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinderIndex
    (m q : Nat) (i₀ : Fin m)
    (_observer : V13RealLinearSequentialRowObserver m q) (_t : Fin q) where
  A : V13RealLinearNoTargetRowsMap m i₀
  rows : Finset (Fin m)
  row : Fin m
  hit : V13RealLinearRowFunctionalTargetCosetHit A.val rows i₀ row
  transcript : V13RealLinearRowsTranscriptSpace m rows

noncomputable instance
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q) :
    Fintype
      (V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinderIndex
        m q i₀ observer t) := by
  classical
  let Index :=
    V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinderIndex
      m q i₀ observer t
  let SigmaIndex :=
    Σ A : V13RealLinearNoTargetRowsMap m i₀,
      Σ rows : Finset (Fin m),
        Σ row :
          {row : Fin m //
            V13RealLinearRowFunctionalTargetCosetHit A.val rows i₀ row},
          V13RealLinearRowsTranscriptSpace m rows
  exact
    Fintype.ofEquiv SigmaIndex
      { toFun := fun idx =>
          { A := idx.1
            rows := idx.2.1
            row := idx.2.2.1.val
            hit := idx.2.2.1.property
            transcript := idx.2.2.2 }
        invFun := fun idx =>
          ⟨idx.A, idx.rows, ⟨idx.row, idx.hit⟩, idx.transcript⟩
        left_inv := by
          intro idx
          rcases idx with ⟨A, rows, row, transcript⟩
          cases row
          rfl
        right_inv := by
          intro idx
          cases idx
          rfl }

/-- Hidden-vector cylinder for a fixed no-target map and fixed transcript
index.  The rowset, hit row, and transcript are fixed in the index; the only
remaining choices are hidden vectors whose induced sequential trace lands in
that cell. -/
abbrev
    V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinder
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (idx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinderIndex
        m q i₀ observer t) :=
  {x : F2Vec m //
    let omega :
        V13RealLinearAdaptiveQRowWorld m
          (V13RealLinearNoTargetRowsMap m i₀) := (idx.A, x)
    V13RealLinearAdaptiveQRowTraceFirstCosetHit
      (v13RealLinearNoTargetRowsSequentialQRowExperiment i₀ observer)
      i₀
      (v13RealLinearNoTargetRowsSequentialQRowTrace i₀ observer)
      t omega ∧
    v13RealLinearRowTracePrefixRows
      (v13RealLinearNoTargetRowsSequentialQRowTrace i₀ observer omega)
      (t : Nat) = idx.rows ∧
    (∃ h : (t : Nat) <
        (v13RealLinearNoTargetRowsSequentialQRowTrace i₀ observer omega).length,
      (v13RealLinearNoTargetRowsSequentialQRowTrace i₀ observer omega).get
        ⟨(t : Nat), h⟩ = idx.row) ∧
    v13RealLinearRowsTranscript idx.rows
        (v13RealLinearPublicInput
          ({ x := x, A := idx.A.val } : V13RealLinearWorld m)) =
      idx.transcript}

noncomputable instance
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (idx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinderIndex
        m q i₀ observer t) :
    Fintype
      (V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinder
        i₀ observer t idx) := by
  classical
  unfold
    V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinder
  infer_instance

noncomputable def
    v13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinderToUnreadAssignment
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (idx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinderIndex
        m q i₀ observer t) :
    V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinder
        i₀ observer t idx ↪
      V13RealLinearRowsUnreadAssignment m idx.rows where
  toFun x := fun unread => idx.A.val.toEquiv x.val unread.1
  inj' := by
    classical
    intro x y hassign
    apply Subtype.ext
    apply idx.A.val.toEquiv.injective
    funext row
    by_cases hrow : row ∈ idx.rows
    · have htranscript :
          v13RealLinearRowsTranscript idx.rows
              (v13RealLinearPublicInput
                ({ x := x.val, A := idx.A.val } : V13RealLinearWorld m)) =
            v13RealLinearRowsTranscript idx.rows
              (v13RealLinearPublicInput
                ({ x := y.val, A := idx.A.val } : V13RealLinearWorld m)) :=
        x.property.2.2.2.trans y.property.2.2.2.symm
      have hview := congrFun htranscript ⟨row, hrow⟩
      simpa [v13RealLinearRowsTranscript, v13RealLinearRowView,
        v13RealLinearPublicInput] using congrArg Prod.snd hview
    · exact congrFun hassign ⟨row, hrow⟩

theorem
    v13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinder_card_le_capacity
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (idx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinderIndex
        m q i₀ observer t) :
    Fintype.card
        (V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinder
          i₀ observer t idx) ≤
      2 ^ (m - idx.rows.card) := by
  classical
  have hle :
      Fintype.card
          (V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinder
            i₀ observer t idx) ≤
        Fintype.card (V13RealLinearRowsUnreadAssignment m idx.rows) :=
    Fintype.card_le_of_embedding
      (v13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinderToUnreadAssignment
        i₀ observer t idx)
  exact hle.trans_eq (v13RealLinearRowsUnreadAssignment_card idx.rows)

/-- Active fixed-map transcript cylinders are the inhabited cylinders.  Charging
capacity only to active cylinders matches the target-case packing interface and
avoids spending capacity on syntactic transcripts that no hidden vector
realizes. -/
abbrev
    V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q) :=
  {idx :
    V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinderIndex
      m q i₀ observer t //
    Nonempty
      (V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinder
        i₀ observer t idx)}

noncomputable instance
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q) :
    Fintype
      (V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t) := by
  classical
  unfold
    V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
  infer_instance

noncomputable def
    v13RealLinearRowsUnreadAssignmentToActiveNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinder
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t) :
    V13RealLinearRowsUnreadAssignment m activeIdx.1.rows ↪
      V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinder
        i₀ observer t activeIdx.1 where
  toFun assignment := by
    classical
    let idx := activeIdx.1
    let witness :
        V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinder
          i₀ observer t idx :=
      Classical.choice activeIdx.2
    let publicW :=
      v13RealLinearPublicInput
        ({ x := witness.val, A := idx.A.val } : V13RealLinearWorld m)
    let b : F2Vec m :=
      v13RealLinearRowsTranscriptCompletion idx.transcript assignment
    let z : F2Vec m := idx.A.val.toEquiv.symm b
    let publicZ :=
      v13RealLinearPublicInput
        ({ x := z, A := idx.A.val } : V13RealLinearWorld m)
    let traceW :=
      v13RealLinearNoTargetRowsSequentialQRowTrace i₀ observer
        (idx.A, witness.val)
    let traceZ :=
      v13RealLinearNoTargetRowsSequentialQRowTrace i₀ observer
        (idx.A, z)
    have htranscriptZ :
        v13RealLinearRowsTranscript idx.rows publicZ = idx.transcript := by
      funext row
      apply Prod.ext
      · have hwitnessView := congrFun witness.property.2.2.2 row
        simpa [publicW, publicZ, v13RealLinearRowsTranscript,
          v13RealLinearRowView, v13RealLinearPublicInput] using
          congrArg Prod.fst hwitnessView
      · change idx.A.val.toEquiv z row.1 = (idx.transcript row).2
        calc
          idx.A.val.toEquiv z row.1 =
              v13RealLinearRowsTranscriptCompletion idx.transcript
                assignment row.1 := by
            simp [z, b]
          _ = (idx.transcript row).2 :=
            v13RealLinearRowsTranscriptCompletion_of_mem
              idx.transcript assignment row.property
    have htraceRowsW :
        v13RealLinearRowTracePrefixRows traceW (t : Nat) = idx.rows := by
      simpa [traceW, idx] using witness.property.2.1
    have hprefixRowsW :
        v13RealLinearSequentialRowTranscriptRows
            (v13RealLinearSequentialRowPrefixTranscriptOf
              observer publicW (t : Nat)) =
          idx.rows := by
      have htraceToTranscript :
          v13RealLinearRowTracePrefixRows traceW (t : Nat) =
            v13RealLinearSequentialRowTranscriptRows
              (v13RealLinearSequentialRowPrefixTranscriptOf
                observer publicW (t : Nat)) := by
        simpa [traceW, publicW,
          v13RealLinearNoTargetRowsSequentialQRowTrace] using
          v13RealLinearSequentialRowTracePrefixRows_eq_prefixTranscriptRows
            observer publicW (Nat.le_of_lt t.isLt)
      exact htraceToTranscript.symm.trans htraceRowsW
    have hsameRows :
        v13RealLinearRowsTranscript
            (v13RealLinearSequentialRowTranscriptRows
              (v13RealLinearSequentialRowPrefixTranscriptOf
                observer publicW (t : Nat))) publicW =
          v13RealLinearRowsTranscript
            (v13RealLinearSequentialRowTranscriptRows
              (v13RealLinearSequentialRowPrefixTranscriptOf
                observer publicW (t : Nat))) publicZ := by
      rw [hprefixRowsW]
      exact witness.property.2.2.2.trans htranscriptZ.symm
    have hprefixTranscript :
        v13RealLinearSequentialRowPrefixTranscriptOf
            observer publicZ (t : Nat) =
          v13RealLinearSequentialRowPrefixTranscriptOf
            observer publicW (t : Nat) := by
      simpa [v13RealLinearSequentialRowPrefixTranscriptOf] using
        v13RealLinearSequentialRowRunAux_eq_of_final_rowsTranscript_eq
          observer publicW publicZ (t : Nat) [] hsameRows
    have htraceRowsZ :
        v13RealLinearRowTracePrefixRows traceZ (t : Nat) = idx.rows := by
      have htraceToTranscript :
          v13RealLinearRowTracePrefixRows traceZ (t : Nat) =
            v13RealLinearSequentialRowTranscriptRows
              (v13RealLinearSequentialRowPrefixTranscriptOf
                observer publicZ (t : Nat)) := by
        simpa [traceZ, publicZ,
          v13RealLinearNoTargetRowsSequentialQRowTrace] using
          v13RealLinearSequentialRowTracePrefixRows_eq_prefixTranscriptRows
            observer publicZ (Nat.le_of_lt t.isLt)
      calc
        v13RealLinearRowTracePrefixRows traceZ (t : Nat) =
            v13RealLinearSequentialRowTranscriptRows
              (v13RealLinearSequentialRowPrefixTranscriptOf
                observer publicZ (t : Nat)) := htraceToTranscript
        _ =
            v13RealLinearSequentialRowTranscriptRows
              (v13RealLinearSequentialRowPrefixTranscriptOf
                observer publicW (t : Nat)) := by rw [hprefixTranscript]
        _ = idx.rows := hprefixRowsW
    have hgetZ :
        ∃ h : (t : Nat) < traceZ.length,
          traceZ.get ⟨(t : Nat), h⟩ = idx.row := by
      rcases witness.property.2.2.1 with ⟨hlenW, hgetW⟩
      have hlenZ : (t : Nat) < traceZ.length := by
        simp [traceZ, v13RealLinearNoTargetRowsSequentialQRowTrace,
          v13RealLinearSequentialRowTraceOf_length]
      refine ⟨hlenZ, ?_⟩
      have hchooseZ :
          traceZ.get ⟨(t : Nat), hlenZ⟩ =
            observer.chooseRow
              (v13RealLinearSequentialRowPrefixTranscriptOf
                observer publicZ (t : Nat)) := by
        simpa [traceZ, publicZ,
          v13RealLinearNoTargetRowsSequentialQRowTrace] using
          v13RealLinearSequentialRowTraceOf_get_eq_chooseRow
            observer publicZ t.isLt
      have hchooseW :
          traceW.get ⟨(t : Nat), hlenW⟩ =
            observer.chooseRow
              (v13RealLinearSequentialRowPrefixTranscriptOf
                observer publicW (t : Nat)) := by
        simpa [traceW, publicW,
          v13RealLinearNoTargetRowsSequentialQRowTrace] using
          v13RealLinearSequentialRowTraceOf_get_eq_chooseRow
            observer publicW t.isLt
      calc
        traceZ.get ⟨(t : Nat), hlenZ⟩ =
            observer.chooseRow
              (v13RealLinearSequentialRowPrefixTranscriptOf
                observer publicZ (t : Nat)) := hchooseZ
        _ =
            observer.chooseRow
              (v13RealLinearSequentialRowPrefixTranscriptOf
                observer publicW (t : Nat)) := by rw [hprefixTranscript]
        _ = traceW.get ⟨(t : Nat), hlenW⟩ := hchooseW.symm
        _ = idx.row := hgetW
    have hfirstZ :
        V13RealLinearAdaptiveQRowTraceFirstCosetHit
          (v13RealLinearNoTargetRowsSequentialQRowExperiment i₀ observer)
          i₀
          (v13RealLinearNoTargetRowsSequentialQRowTrace i₀ observer)
          t (idx.A, z) := by
      have hlenZ : (t : Nat) < traceZ.length := by
        simp [traceZ, v13RealLinearNoTargetRowsSequentialQRowTrace,
          v13RealLinearSequentialRowTraceOf_length]
      constructor
      · simpa [traceZ] using hlenZ
      · rcases hgetZ with ⟨hlenGet, hget⟩
        refine ⟨hlenGet, ?_⟩
        have hhit :
            V13RealLinearRowFunctionalTargetCosetHit idx.A.val idx.rows i₀
              (traceZ.get ⟨(t : Nat), hlenGet⟩) := by
          rw [hget]
          exact idx.hit
        simpa [traceZ, htraceRowsZ,
          v13RealLinearNoTargetRowsSequentialQRowExperiment,
          v13RealLinearNoTargetRowsCausalQRowExperiment,
          v13RealLinearNoTargetRowsQRowExperiment] using hhit
    exact
      ⟨z, by
        exact ⟨hfirstZ, htraceRowsZ, hgetZ, htranscriptZ⟩⟩
  inj' := by
    classical
    intro assignment₀ assignment₁ hcell
    let idx := activeIdx.1
    funext row
    have hz :
        idx.A.val.toEquiv.symm
            (v13RealLinearRowsTranscriptCompletion
              idx.transcript assignment₀) =
          idx.A.val.toEquiv.symm
            (v13RealLinearRowsTranscriptCompletion
              idx.transcript assignment₁) := by
      simpa [idx] using
        congrArg
          (fun cell :
            V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinder
              i₀ observer t activeIdx.1 => cell.val)
          hcell
    have hAraw := congrFun (congrArg idx.A.val.toEquiv hz) row.1
    have hA :
        v13RealLinearRowsTranscriptCompletion idx.transcript
            assignment₀ row.1 =
          v13RealLinearRowsTranscriptCompletion idx.transcript
            assignment₁ row.1 := by
      simpa using hAraw
    calc
      assignment₀ row =
          v13RealLinearRowsTranscriptCompletion idx.transcript
            assignment₀ row.1 := by
        exact
          (v13RealLinearRowsTranscriptCompletion_of_not_mem
            idx.transcript assignment₀ row).symm
      _ =
          v13RealLinearRowsTranscriptCompletion idx.transcript
            assignment₁ row.1 := hA
      _ = assignment₁ row :=
          v13RealLinearRowsTranscriptCompletion_of_not_mem
            idx.transcript assignment₁ row

theorem
    v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_capacity_le_card
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t) :
    2 ^ (m - activeIdx.1.rows.card) ≤
      Fintype.card
        (V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinder
          i₀ observer t activeIdx.1) := by
  classical
  have hle :
      Fintype.card (V13RealLinearRowsUnreadAssignment m activeIdx.1.rows) ≤
        Fintype.card
          (V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinder
            i₀ observer t activeIdx.1) :=
    Fintype.card_le_of_embedding
      (v13RealLinearRowsUnreadAssignmentToActiveNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinder
        i₀ observer t activeIdx)
  simpa [v13RealLinearRowsUnreadAssignment_card] using hle

theorem
    v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_card_eq_capacity
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t) :
    Fintype.card
        (V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinder
          i₀ observer t activeIdx.1) =
      2 ^ (m - activeIdx.1.rows.card) := by
  exact
    le_antisymm
      (v13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinder_card_le_capacity
        i₀ observer t activeIdx.1)
      (v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_capacity_le_card
        i₀ observer t activeIdx)

theorem
    v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_rows_card_le_step
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t) :
    activeIdx.1.rows.card ≤ (t : Nat) := by
  classical
  rcases activeIdx.2 with ⟨x⟩
  let trace :=
    v13RealLinearNoTargetRowsSequentialQRowTrace i₀ observer
      (activeIdx.1.A, x.val)
  have hprefix :
      v13RealLinearRowTracePrefixRows trace (t : Nat) =
        activeIdx.1.rows := by
    simpa [trace] using x.property.2.1
  rw [← hprefix]
  exact v13RealLinearRowTracePrefixRows_card_le trace (t : Nat)

theorem
    v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_rows_nonempty
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t) :
    activeIdx.1.rows.Nonempty := by
  classical
  by_contra hrows
  have hrowsEmpty : activeIdx.1.rows = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp hrows
  have hhit : V13RealLinearRowFunctionalTargetCosetHit
      activeIdx.1.A.val ∅ i₀ activeIdx.1.row := by
    simpa [hrowsEmpty] using activeIdx.1.hit
  exact
    v13RealLinearNoTargetRows_rowFunctionalTargetCosetHit_empty_false
      i₀ activeIdx.1.row activeIdx.1.A hhit

theorem
    v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_rows_card_pos
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t) :
    0 < activeIdx.1.rows.card := by
  exact
    Finset.card_pos.mpr
      (v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_rows_nonempty
        i₀ observer t activeIdx)

theorem
    v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_step_pos
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t) :
    0 < (t : Nat) :=
  (v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_rows_card_pos
      i₀ observer t activeIdx).trans_le
    (v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_rows_card_le_step
      i₀ observer t activeIdx)

theorem
    v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_insert_rowsGenerateTarget
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t) :
    V13RealLinearRowsGenerateTarget activeIdx.1.A.val
      (insert activeIdx.1.row activeIdx.1.rows) i₀ :=
  v13RealLinear_rowsGenerateTarget_insert_of_rowFunctionalTargetCosetHit
    activeIdx.1.A.val activeIdx.1.rows i₀ activeIdx.1.row activeIdx.1.hit

theorem
    v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_insert_rows_card_le_step_succ
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t) :
    (insert activeIdx.1.row activeIdx.1.rows).card ≤ (t : Nat) + 1 := by
  classical
  have hrows :=
    v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_rows_card_le_step
      i₀ observer t activeIdx
  by_cases hrow : activeIdx.1.row ∈ activeIdx.1.rows
  · rw [Finset.insert_eq_of_mem hrow]
    omega
  · rw [Finset.card_insert_of_notMem hrow]
    omega

def
    v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedBudgetedRowset
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t) :
    V13RealLinearBudgetedRowset m ((t : Nat) + 1) :=
  ⟨insert activeIdx.1.row activeIdx.1.rows,
    v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_insert_rows_card_le_step_succ
      i₀ observer t activeIdx⟩

def
    v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedMap
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t) :
    V13RealLinearNoTargetBudgetedRowsetGeneratingMapSet i₀
      (v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedBudgetedRowset
        i₀ observer t activeIdx) :=
  ⟨activeIdx.1.A,
    v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_insert_rowsGenerateTarget
      i₀ observer t activeIdx⟩

theorem
    v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_insert_rows_card_le_budget
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t) :
    (insert activeIdx.1.row activeIdx.1.rows).card ≤ q := by
  have hstep :=
    v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_insert_rows_card_le_step_succ
      i₀ observer t activeIdx
  have hbudget : (t : Nat) + 1 ≤ q :=
    Nat.succ_le_of_lt t.isLt
  exact hstep.trans hbudget

def
    v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedQBudgetedRowset
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t) :
    V13RealLinearBudgetedRowset m q :=
  ⟨insert activeIdx.1.row activeIdx.1.rows,
    v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_insert_rows_card_le_budget
      i₀ observer t activeIdx⟩

def
    v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedQMap
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t) :
    V13RealLinearNoTargetBudgetedRowsetGeneratingMapSet i₀
      (v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedQBudgetedRowset
        i₀ observer t activeIdx) :=
  ⟨activeIdx.1.A,
    v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_insert_rowsGenerateTarget
      i₀ observer t activeIdx⟩

theorem
    v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_existing_rowsGenerateTarget
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t)
    (hrow : activeIdx.1.row ∈ activeIdx.1.rows) :
    V13RealLinearRowsGenerateTarget activeIdx.1.A.val activeIdx.1.rows i₀ :=
  v13RealLinear_rowsGenerateTarget_of_rowFunctionalTargetCosetHit_of_mem
    activeIdx.1.A.val i₀ activeIdx.1.row hrow activeIdx.1.hit

theorem
    v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_fresh_not_rowsGenerateTarget
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t)
    (hrow : activeIdx.1.row ∉ activeIdx.1.rows) :
    ¬ V13RealLinearRowsGenerateTarget activeIdx.1.A.val activeIdx.1.rows i₀ :=
  v13RealLinear_not_rowsGenerateTarget_of_rowFunctionalTargetCosetHit_of_not_mem
    activeIdx.1.A.val i₀ activeIdx.1.row hrow activeIdx.1.hit

theorem
    v13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinder_newCapture_or_priorNewCapture
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (idx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinderIndex
        m q i₀ observer t)
    (cell :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinder
        i₀ observer t idx) :
    V13RealLinearRowTraceNewCapture idx.A.val i₀
        (v13RealLinearNoTargetRowsSequentialQRowTrace i₀ observer
          (idx.A, cell.val))
        (t : Nat) ∨
      ∃ s : Fin (t : Nat),
        V13RealLinearRowTraceNewCapture idx.A.val i₀
          (v13RealLinearNoTargetRowsSequentialQRowTrace i₀ observer
            (idx.A, cell.val))
          s := by
  let trace :=
    v13RealLinearNoTargetRowsSequentialQRowTrace i₀ observer
      (idx.A, cell.val)
  have hcoset :
      V13RealLinearRowTraceCosetHit idx.A.val i₀ trace (t : Nat) := by
    simpa [trace, v13RealLinearNoTargetRowsSequentialQRowExperiment,
      v13RealLinearNoTargetRowsCausalQRowExperiment,
      v13RealLinearNoTargetRowsQRowExperiment] using cell.property.1.2
  simpa [trace] using
    v13RealLinearRowTraceCosetHit_newCapture_or_priorNewCapture
      idx.A.val i₀ trace hcoset

theorem
    v13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinder_existing_priorNewCapture
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (idx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinderIndex
        m q i₀ observer t)
    (cell :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinder
        i₀ observer t idx)
    (hrow : idx.row ∈ idx.rows) :
    ∃ s : Fin (t : Nat),
      V13RealLinearRowTraceNewCapture idx.A.val i₀
        (v13RealLinearNoTargetRowsSequentialQRowTrace i₀ observer
          (idx.A, cell.val))
        s := by
  let trace :=
    v13RealLinearNoTargetRowsSequentialQRowTrace i₀ observer
      (idx.A, cell.val)
  have hsplit :=
    v13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinder_newCapture_or_priorNewCapture
      i₀ observer t idx cell
  cases hsplit with
  | inr hprior => exact hprior
  | inl hnew =>
      have hlen : (t : Nat) < trace.length := by
        simpa [trace] using cell.property.1.1
      have hnotMem :
          trace.get ⟨(t : Nat), hlen⟩ ∉
            v13RealLinearRowTracePrefixRows trace (t : Nat) :=
        v13RealLinearRowTraceNewCapture_get_not_mem
          idx.A.val i₀ trace hlen (by simpa [trace] using hnew)
      have hgetEq :
          trace.get ⟨(t : Nat), hlen⟩ = idx.row := by
        rcases cell.property.2.2.1 with ⟨hrowLen, hget⟩
        have hidx :
            (⟨(t : Nat), hlen⟩ : Fin trace.length) =
              ⟨(t : Nat), by simpa [trace] using hrowLen⟩ := by
          apply Fin.ext
          rfl
        calc
          trace.get ⟨(t : Nat), hlen⟩ =
              trace.get ⟨(t : Nat), by simpa [trace] using hrowLen⟩ := by
                rw [hidx]
          _ = idx.row := by simpa [trace] using hget
      have hmem :
          trace.get ⟨(t : Nat), hlen⟩ ∈
            v13RealLinearRowTracePrefixRows trace (t : Nat) := by
        have hprefix :
            v13RealLinearRowTracePrefixRows trace (t : Nat) = idx.rows := by
          simpa [trace] using cell.property.2.1
        rw [hgetEq, hprefix]
        exact hrow
      exact False.elim (hnotMem hmem)

theorem
    v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_fresh_insert_rows_card_two_le
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t)
    (hrow : activeIdx.1.row ∉ activeIdx.1.rows) :
    2 ≤ (insert activeIdx.1.row activeIdx.1.rows).card := by
  have hpos :=
    v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_rows_card_pos
      i₀ observer t activeIdx
  rw [Finset.card_insert_of_notMem hrow]
  omega

theorem
    v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_existing_rows_card_two_le
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t)
    (hrow : activeIdx.1.row ∈ activeIdx.1.rows) :
    2 ≤ activeIdx.1.rows.card := by
  have hgen :=
    v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_existing_rowsGenerateTarget
      i₀ observer t activeIdx hrow
  have hnotOne :
      ¬ activeIdx.1.rows.card ≤ 1 := by
    intro hle
    exact
      (v13RealLinearNoTargetRows_not_rowsGenerateTarget_of_rows_card_le_one
        i₀ activeIdx.1.A hle) hgen
  omega

theorem
    v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_insert_rows_card_two_le
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t) :
    2 ≤ (insert activeIdx.1.row activeIdx.1.rows).card := by
  classical
  by_cases hrow : activeIdx.1.row ∈ activeIdx.1.rows
  · rw [Finset.insert_eq_of_mem hrow]
    exact
      v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_existing_rows_card_two_le
        i₀ observer t activeIdx hrow
  · exact
      v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_fresh_insert_rows_card_two_le
        i₀ observer t activeIdx hrow

theorem
    v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedQBudgetedRowset_card_two_le
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t) :
    2 ≤
      (v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedQBudgetedRowset
        i₀ observer t activeIdx).1.card := by
  simpa [
    v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedQBudgetedRowset]
    using
      v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_insert_rows_card_two_le
        i₀ observer t activeIdx

theorem
    v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_capacity_le_two_mul_insert_capacity
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t) :
    2 ^ (m - activeIdx.1.rows.card) ≤
      2 * 2 ^ (m - (insert activeIdx.1.row activeIdx.1.rows).card) := by
  classical
  by_cases hrow : activeIdx.1.row ∈ activeIdx.1.rows
  · rw [Finset.insert_eq_of_mem hrow]
    nlinarith [show 0 < 2 ^ (m - activeIdx.1.rows.card) by positivity]
  · have hcardLe :
        (insert activeIdx.1.row activeIdx.1.rows).card ≤ m := by
      have hcardLeUniv :
          (insert activeIdx.1.row activeIdx.1.rows : Finset (Fin m)).card ≤
            Fintype.card (Fin m) :=
        Finset.card_le_univ _
      simpa using hcardLeUniv
    have hsuccLe : activeIdx.1.rows.card + 1 ≤ m := by
      simpa [Finset.card_insert_of_notMem hrow] using hcardLe
    have hsub :
        m - activeIdx.1.rows.card =
          (m - (activeIdx.1.rows.card + 1)) + 1 := by
      omega
    rw [Finset.card_insert_of_notMem hrow, hsub, pow_succ]
    rw [Nat.mul_comm (2 ^ (m - (activeIdx.1.rows.card + 1))) 2]

theorem
    v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_capacity_le_two_mul_generatedQBudgetedRowset_capacity
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t) :
    2 ^ (m - activeIdx.1.rows.card) ≤
      2 *
        2 ^ (m -
          (v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedQBudgetedRowset
            i₀ observer t activeIdx).1.card) := by
  simpa [
    v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedQBudgetedRowset]
    using
      v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_capacity_le_two_mul_insert_capacity
        i₀ observer t activeIdx

theorem
    v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_sum_capacity_le_two_mul_generatedQBudgetedRowset_capacity_sum
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q) :
    (∑ activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t,
      2 ^ (m - activeIdx.1.rows.card)) ≤
      2 *
        ∑ activeIdx :
          V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
            i₀ observer t,
          2 ^ (m -
            (v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedQBudgetedRowset
              i₀ observer t activeIdx).1.card) := by
  classical
  calc
    (∑ activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t,
      2 ^ (m - activeIdx.1.rows.card)) ≤
        ∑ activeIdx :
          V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
            i₀ observer t,
          2 *
            2 ^ (m -
              (v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedQBudgetedRowset
                i₀ observer t activeIdx).1.card) := by
          apply Finset.sum_le_sum
          intro activeIdx _hactiveIdx
          exact
            v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_capacity_le_two_mul_generatedQBudgetedRowset_capacity
              i₀ observer t activeIdx
    _ =
      2 *
        ∑ activeIdx :
          V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
            i₀ observer t,
          2 ^ (m -
            (v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedQBudgetedRowset
              i₀ observer t activeIdx).1.card) := by
      rw [Finset.mul_sum]

theorem
    v13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinder_sum_card_eq_active_capacity
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q) :
    (∑ idx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinderIndex
        m q i₀ observer t,
      Fintype.card
        (V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinder
          i₀ observer t idx)) =
      ∑ activeIdx :
        V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
          i₀ observer t,
        2 ^ (m - activeIdx.1.rows.card) := by
  classical
  let Index :=
    V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinderIndex
      m q i₀ observer t
  let Cell : Index → Type := fun idx =>
    V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinder
      i₀ observer t idx
  let active : Index → Prop := fun idx => Nonempty (Cell idx)
  let mass : Index → Nat := fun idx => Fintype.card (Cell idx)
  let capacity : Index → Nat := fun idx => 2 ^ (m - idx.rows.card)
  have hsplit :
      (∑ idx : Index, mass idx) =
        (∑ idx : {idx : Index // active idx}, mass idx.1) +
          ∑ idx : {idx : Index // ¬ active idx}, mass idx.1 := by
    exact (Fintype.sum_subtype_add_sum_subtype active mass).symm
  have hinactive :
      (∑ idx : {idx : Index // ¬ active idx}, mass idx.1) = 0 := by
    apply Finset.sum_eq_zero
    intro idx _hidx
    dsimp [mass, Cell, active] at *
    rw [Fintype.card_eq_zero_iff]
    exact ⟨fun x => idx.property ⟨x⟩⟩
  have hactiveEq :
      (∑ idx : {idx : Index // active idx}, mass idx.1) =
        ∑ idx : {idx : Index // active idx}, capacity idx.1 := by
    apply Finset.sum_congr rfl
    intro idx _hidx
    dsimp [mass, capacity, Cell, active]
    exact
      v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_card_eq_capacity
        i₀ observer t idx
  calc
    (∑ idx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinderIndex
        m q i₀ observer t,
      Fintype.card
        (V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinder
          i₀ observer t idx)) =
        ∑ idx : Index, mass idx := rfl
    _ =
        (∑ idx : {idx : Index // active idx}, mass idx.1) +
          ∑ idx : {idx : Index // ¬ active idx}, mass idx.1 := hsplit
    _ =
        (∑ idx : {idx : Index // active idx}, mass idx.1) + 0 := by
          rw [hinactive]
    _ =
        ∑ idx : {idx : Index // active idx}, mass idx.1 := by simp
    _ =
        ∑ idx : {idx : Index // active idx}, capacity idx.1 := hactiveEq
    _ =
        ∑ activeIdx :
          V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
            i₀ observer t,
          2 ^ (m - activeIdx.1.rows.card) := rfl

theorem
    v13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixWorldSet_cosetHit
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (rows : Finset (Fin m)) (row : Fin m)
    (omega :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixWorldSet
        i₀ observer t rows row) :
    V13RealLinearRowFunctionalTargetCosetHit omega.val.1.val rows i₀ row := by
  classical
  let trace :=
    v13RealLinearNoTargetRowsSequentialQRowTrace i₀ observer omega.val
  rcases omega.property with ⟨hfirst, hrows, hrow⟩
  rcases hfirst.2 with ⟨hhitIndex, hhit⟩
  rcases hrow with ⟨hrowIndex, hget⟩
  have hidx :
      (⟨(t : Nat), hhitIndex⟩ : Fin trace.length) =
        ⟨(t : Nat), hrowIndex⟩ := by
    apply Fin.ext
    rfl
  have hhitRows :
      V13RealLinearRowFunctionalTargetCosetHit
        ((v13RealLinearNoTargetRowsSequentialQRowExperiment
            i₀ observer).sampleA omega.val.1)
        rows i₀ (trace.get ⟨(t : Nat), hhitIndex⟩) := by
    simpa [trace, hrows] using hhit
  have hgetHit : trace.get ⟨(t : Nat), hhitIndex⟩ = row := by
    simpa [trace, hidx] using hget
  rw [hgetHit] at hhitRows
  simpa [v13RealLinearNoTargetRowsSequentialQRowExperiment,
    v13RealLinearNoTargetRowsCausalQRowExperiment,
    v13RealLinearNoTargetRowsQRowExperiment] using hhitRows

noncomputable def
    v13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixTranscriptSigmaEquivFixedMapCylinderSigma
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q) :
    (Σ rows : Finset (Fin m),
      Σ row : Fin m,
        Σ transcript : V13RealLinearRowsTranscriptSpace m rows,
          V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixTranscriptWorldSet
            i₀ observer t rows row transcript) ≃
      (Σ idx :
        V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinderIndex
          m q i₀ observer t,
        V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinder
          i₀ observer t idx) where
  toFun cell := by
    rcases cell with ⟨rows, row, transcript, cell⟩
    let idx :
        V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinderIndex
          m q i₀ observer t :=
      { A := cell.val.val.1
        rows := rows
        row := row
        hit :=
          v13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixWorldSet_cosetHit
            i₀ observer t rows row cell.val
        transcript := transcript }
    exact
      ⟨idx,
        ⟨cell.val.val.2, by
          dsimp [idx,
            V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinder]
          exact
            ⟨cell.val.property.1, cell.val.property.2.1,
              cell.val.property.2.2, cell.property⟩⟩⟩
  invFun cell := by
    rcases cell with ⟨idx, cell⟩
    exact
      ⟨idx.rows, idx.row, idx.transcript,
        ⟨⟨(idx.A, cell.val),
          ⟨cell.property.1, cell.property.2.1,
            cell.property.2.2.1⟩⟩,
          cell.property.2.2.2⟩⟩
  left_inv cell := by
    rcases cell with ⟨rows, row, transcript, cell⟩
    rcases cell with ⟨omega, htranscript⟩
    cases htranscript
    rfl
  right_inv cell := by
    rcases cell with ⟨idx, cell⟩
    apply Sigma.ext
    · cases idx
      rfl
    · simp

theorem
    v13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixTranscriptWorldSet_sum_card_eq_fixedMapCylinder_sum_card
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q) :
    (∑ rows : Finset (Fin m),
      ∑ row : Fin m,
        ∑ transcript : V13RealLinearRowsTranscriptSpace m rows,
          Fintype.card
            (V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixTranscriptWorldSet
              i₀ observer t rows row transcript)) =
      ∑ idx :
        V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinderIndex
          m q i₀ observer t,
        Fintype.card
          (V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinder
            i₀ observer t idx) := by
  classical
  have hcard :
      Fintype.card
          (Σ rows : Finset (Fin m),
            Σ row : Fin m,
              Σ transcript : V13RealLinearRowsTranscriptSpace m rows,
                V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixTranscriptWorldSet
                  i₀ observer t rows row transcript) =
        Fintype.card
          (Σ idx :
            V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinderIndex
              m q i₀ observer t,
            V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinder
              i₀ observer t idx) :=
    Fintype.card_congr
      (v13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixTranscriptSigmaEquivFixedMapCylinderSigma
        i₀ observer t)
  simpa [Fintype.card_sigma] using hcard

theorem
    v13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixTranscriptWorldSet_sum_card_eq_active_capacity
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q) :
    (∑ rows : Finset (Fin m),
      ∑ row : Fin m,
        ∑ transcript : V13RealLinearRowsTranscriptSpace m rows,
          Fintype.card
            (V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixTranscriptWorldSet
              i₀ observer t rows row transcript)) =
      ∑ activeIdx :
        V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
          i₀ observer t,
        2 ^ (m - activeIdx.1.rows.card) := by
  rw [
    v13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixTranscriptWorldSet_sum_card_eq_fixedMapCylinder_sum_card
      i₀ observer t,
    v13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinder_sum_card_eq_active_capacity
      i₀ observer t]

noncomputable def
    v13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixWorldSetEquivSigmaTranscript
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (rows : Finset (Fin m)) (row : Fin m) :
    V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixWorldSet
        i₀ observer t rows row ≃
      (Σ transcript : V13RealLinearRowsTranscriptSpace m rows,
        V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixTranscriptWorldSet
          i₀ observer t rows row transcript) where
  toFun omega := by
    classical
    exact
      ⟨v13RealLinearRowsTranscript rows
          (v13RealLinearPublicInput
            ({ x := omega.val.2, A := omega.val.1.val } :
              V13RealLinearWorld m)),
        ⟨omega, rfl⟩⟩
  invFun cell := by
    rcases cell with ⟨_transcript, cell⟩
    exact cell.val
  left_inv _omega := by
    rfl
  right_inv cell := by
    rcases cell with ⟨transcript, cell⟩
    rcases cell with ⟨omega, htranscript⟩
    cases htranscript
    rfl

theorem
    v13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixWorldSet_card_eq_sum_transcripts
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (rows : Finset (Fin m)) (row : Fin m) :
    Fintype.card
        (V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixWorldSet
          i₀ observer t rows row) =
      ∑ transcript : V13RealLinearRowsTranscriptSpace m rows,
        Fintype.card
          (V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixTranscriptWorldSet
            i₀ observer t rows row transcript) := by
  classical
  rw [Fintype.card_congr
    (v13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixWorldSetEquivSigmaTranscript
      i₀ observer t rows row)]
  rw [Fintype.card_sigma]

/-- The full no-target sequential trace-coset hit event at one step. -/
abbrev V13RealLinearNoTargetSequentialTraceFirstCosetHitWorldSet
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q) :=
  {omega :
      V13RealLinearAdaptiveQRowWorld m
        (V13RealLinearNoTargetRowsMap m i₀) //
    V13RealLinearAdaptiveQRowTraceFirstCosetHit
      (v13RealLinearNoTargetRowsSequentialQRowExperiment i₀ observer)
      i₀
      (v13RealLinearNoTargetRowsSequentialQRowTrace i₀ observer)
      t omega}

noncomputable instance
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q) :
    Fintype
      (V13RealLinearNoTargetSequentialTraceFirstCosetHitWorldSet
        i₀ observer t) := by
  classical
  unfold V13RealLinearNoTargetSequentialTraceFirstCosetHitWorldSet
  infer_instance

noncomputable def
    v13RealLinearNoTargetSequentialTraceFirstCosetHitWorldSetEquivSigmaFixedPrefixTranscript
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q) :
    V13RealLinearNoTargetSequentialTraceFirstCosetHitWorldSet
        i₀ observer t ≃
      (Σ rows : Finset (Fin m),
        Σ row : Fin m,
          Σ transcript : V13RealLinearRowsTranscriptSpace m rows,
            V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixTranscriptWorldSet
              i₀ observer t rows row transcript) where
  toFun omega := by
    classical
    let trace :=
      v13RealLinearNoTargetRowsSequentialQRowTrace i₀ observer omega.val
    let rows := v13RealLinearRowTracePrefixRows trace (t : Nat)
    let row := trace.get ⟨(t : Nat), omega.property.1⟩
    let transcript :=
      v13RealLinearRowsTranscript rows
        (v13RealLinearPublicInput
          ({ x := omega.val.2, A := omega.val.1.val } :
            V13RealLinearWorld m))
    exact
      ⟨rows, row, transcript,
        ⟨⟨omega.val,
          ⟨omega.property, rfl, ⟨omega.property.1, rfl⟩⟩⟩,
          rfl⟩⟩
  invFun cell := by
    rcases cell with ⟨_rows, _row, _transcript, cell⟩
    exact ⟨cell.val.val, cell.val.property.1⟩
  left_inv _omega := by
    rfl
  right_inv cell := by
    rcases cell with ⟨rows, row, transcript, cell⟩
    rcases cell with ⟨omegaFixed, htranscript⟩
    rcases omegaFixed with ⟨omega, hfirst, hrows, hrow⟩
    let trace :=
      v13RealLinearNoTargetRowsSequentialQRowTrace i₀ observer omega
    cases hrows
    cases htranscript
    rcases hrow with ⟨hrowLen, hget⟩
    have hidx :
        (⟨(t : Nat), hfirst.1⟩ : Fin trace.length) =
          ⟨(t : Nat), hrowLen⟩ := by
      apply Fin.ext
      rfl
    have hrowEq : trace.get ⟨(t : Nat), hfirst.1⟩ = row := by
      calc
        trace.get ⟨(t : Nat), hfirst.1⟩ =
            trace.get ⟨(t : Nat), hrowLen⟩ := by rw [hidx]
        _ = row := hget
    cases hrowEq
    rfl

theorem
    v13RealLinearNoTargetSequentialTraceFirstCosetHitWorldSet_card_eq_sum_fixedPrefixTranscript
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q) :
    Fintype.card
        (V13RealLinearNoTargetSequentialTraceFirstCosetHitWorldSet
          i₀ observer t) =
      ∑ rows : Finset (Fin m),
        ∑ row : Fin m,
          ∑ transcript : V13RealLinearRowsTranscriptSpace m rows,
            Fintype.card
              (V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixTranscriptWorldSet
                i₀ observer t rows row transcript) := by
  classical
  rw [Fintype.card_congr
    (v13RealLinearNoTargetSequentialTraceFirstCosetHitWorldSetEquivSigmaFixedPrefixTranscript
      i₀ observer t)]
  simp [Fintype.card_sigma]

theorem
    v13RealLinearNoTargetSequentialTraceFirstCosetHitWorldSet_card_eq_active_capacity
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q) :
    Fintype.card
        (V13RealLinearNoTargetSequentialTraceFirstCosetHitWorldSet
          i₀ observer t) =
      ∑ activeIdx :
        V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
          i₀ observer t,
        2 ^ (m - activeIdx.1.rows.card) := by
  rw [
    v13RealLinearNoTargetSequentialTraceFirstCosetHitWorldSet_card_eq_sum_fixedPrefixTranscript
      i₀ observer t,
    v13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixTranscriptWorldSet_sum_card_eq_active_capacity
      i₀ observer t]

/-- A finite vector presentation of an ordered sequential row transcript
prefix.  Unlike rowset transcripts, this preserves order and repeated reads,
which is exactly the data used by `chooseRow`. -/
abbrev V13RealLinearSequentialPrefixTranscriptVector
    (m n : Nat) :=
  Fin n → Fin m × V13RealLinearRowView m

noncomputable def v13RealLinearSequentialPrefixTranscriptVectorOf
    {m q : Nat} (observer : V13RealLinearSequentialRowObserver m q)
    (publicInput : V13RealLinearPublic m) (n : Nat) :
    V13RealLinearSequentialPrefixTranscriptVector m n :=
  fun k =>
    (v13RealLinearSequentialRowPrefixTranscriptOf
      observer publicInput n).get
      ⟨k.1, by
        simp [v13RealLinearSequentialRowPrefixTranscriptOf_length]⟩

noncomputable def v13RealLinearSequentialPrefixTranscriptVectorToList
    {m n : Nat} (pref : V13RealLinearSequentialPrefixTranscriptVector m n) :
    V13RealLinearSequentialRowTranscript m :=
  List.ofFn pref

noncomputable def v13RealLinearSequentialPrefixTranscriptVectorRows
    {m n : Nat} (pref : V13RealLinearSequentialPrefixTranscriptVector m n) :
    Finset (Fin m) :=
  v13RealLinearSequentialRowTranscriptRows
    (v13RealLinearSequentialPrefixTranscriptVectorToList pref)

noncomputable def v13RealLinearSequentialPrefixTranscriptVectorNextRow
    {m q n : Nat} (observer : V13RealLinearSequentialRowObserver m q)
    (pref : V13RealLinearSequentialPrefixTranscriptVector m n) : Fin m :=
  observer.chooseRow
    (v13RealLinearSequentialPrefixTranscriptVectorToList pref)

noncomputable def v13RealLinearSequentialPrefixTranscriptVectorInit
    {m n : Nat}
    (pref : V13RealLinearSequentialPrefixTranscriptVector m (n + 1)) :
    V13RealLinearSequentialPrefixTranscriptVector m n :=
  fun k => pref k.castSucc

def v13RealLinearSequentialPrefixTranscriptVectorLastRow
    {m n : Nat}
    (pref : V13RealLinearSequentialPrefixTranscriptVector m (n + 1)) :
    Fin m :=
  (pref ⟨n, Nat.lt_succ_self n⟩).1

theorem v13RealLinearSequentialRowRunAuxWithRowView_mem_view
    {m q : Nat} (observer : V13RealLinearSequentialRowObserver m q)
    (rowView : Fin m → V13RealLinearRowView m) (n : Nat)
    (transcript : V13RealLinearSequentialRowTranscript m)
    (htranscript :
      ∀ entry : Fin m × V13RealLinearRowView m,
        entry ∈ transcript → entry.2 = rowView entry.1)
    {entry : Fin m × V13RealLinearRowView m}
    (hentry :
      entry ∈
        v13RealLinearSequentialRowRunAuxWithRowView
          observer rowView n transcript) :
    entry.2 = rowView entry.1 := by
  induction n generalizing transcript with
  | zero =>
      simpa [v13RealLinearSequentialRowRunAuxWithRowView] using
        htranscript entry hentry
  | succ n ih =>
      let row := observer.chooseRow transcript
      exact
        ih (transcript ++ [(row, rowView row)])
          (by
            intro entry hentry
            simp [row] at hentry
            rcases hentry with hentry | hentry
            · exact htranscript entry hentry
            · cases hentry
              rfl)
          (by
            simpa [v13RealLinearSequentialRowRunAuxWithRowView, row] using
              hentry)

theorem v13RealLinearSequentialRowPrefixTranscriptOf_mem_view
    {m q : Nat} (observer : V13RealLinearSequentialRowObserver m q)
    (publicInput : V13RealLinearPublic m) (n : Nat)
    {entry : Fin m × V13RealLinearRowView m}
    (hentry :
      entry ∈
        v13RealLinearSequentialRowPrefixTranscriptOf
          observer publicInput n) :
    entry.2 = v13RealLinearRowView entry.1 publicInput := by
  have hentryWith :
      entry ∈
        v13RealLinearSequentialRowPrefixTranscriptOfWithRowView
          observer (fun row => v13RealLinearRowView row publicInput) n := by
    simpa [v13RealLinearSequentialRowPrefixTranscriptOf_eq_withRowView]
      using hentry
  simpa [v13RealLinearSequentialRowPrefixTranscriptOfWithRowView] using
    v13RealLinearSequentialRowRunAuxWithRowView_mem_view
      observer (fun row => v13RealLinearRowView row publicInput) n []
      (by
        intro entry hentry
        simp at hentry)
      hentryWith

theorem v13RealLinearRowsTranscript_eq_of_sequentialPrefixTranscript_eq
    {m q : Nat} (observer : V13RealLinearSequentialRowObserver m q)
    (public₀ public₁ : V13RealLinearPublic m) (n : Nat)
    (hpref :
      v13RealLinearSequentialRowPrefixTranscriptOf observer public₀ n =
        v13RealLinearSequentialRowPrefixTranscriptOf observer public₁ n) :
    v13RealLinearRowsTranscript
        (v13RealLinearSequentialRowTranscriptRows
          (v13RealLinearSequentialRowPrefixTranscriptOf observer public₀ n))
        public₀ =
      v13RealLinearRowsTranscript
        (v13RealLinearSequentialRowTranscriptRows
          (v13RealLinearSequentialRowPrefixTranscriptOf observer public₀ n))
        public₁ := by
  funext row
  have hrowExists :
      ∃ entry : Fin m × V13RealLinearRowView m,
        entry ∈
            v13RealLinearSequentialRowPrefixTranscriptOf
              observer public₀ n ∧
          entry.1 = row.1 := by
    have hrowMem :
        row.1 ∈
          (v13RealLinearSequentialRowPrefixTranscriptOf
            observer public₀ n).map Prod.fst := by
      simpa only [v13RealLinearSequentialRowTranscriptRows, List.mem_toFinset]
        using row.property
    rcases List.mem_map.mp hrowMem with ⟨entry, hentry, hfst⟩
    exact ⟨entry, hentry, hfst⟩
  rcases hrowExists with ⟨entry, hentry₀, hfst⟩
  have hentry₁ :
      entry ∈
        v13RealLinearSequentialRowPrefixTranscriptOf
          observer public₁ n := by
    simpa [hpref] using hentry₀
  have hview₀ :
      entry.2 = v13RealLinearRowView entry.1 public₀ :=
    v13RealLinearSequentialRowPrefixTranscriptOf_mem_view
      observer public₀ n hentry₀
  have hview₁ :
      entry.2 = v13RealLinearRowView entry.1 public₁ :=
    v13RealLinearSequentialRowPrefixTranscriptOf_mem_view
      observer public₁ n hentry₁
  calc
    v13RealLinearRowsTranscript
        (v13RealLinearSequentialRowTranscriptRows
          (v13RealLinearSequentialRowPrefixTranscriptOf observer public₀ n))
        public₀ row =
      v13RealLinearRowView row.1 public₀ := rfl
    _ = v13RealLinearRowView entry.1 public₀ := by rw [hfst]
    _ = entry.2 := hview₀.symm
    _ = v13RealLinearRowView entry.1 public₁ := hview₁
    _ = v13RealLinearRowView row.1 public₁ := by rw [hfst]
    _ =
      v13RealLinearRowsTranscript
        (v13RealLinearSequentialRowTranscriptRows
          (v13RealLinearSequentialRowPrefixTranscriptOf observer public₀ n))
        public₁ row := rfl

theorem v13RealLinearSequentialPrefixTranscriptVectorOf_toList
    {m q : Nat} (observer : V13RealLinearSequentialRowObserver m q)
    (publicInput : V13RealLinearPublic m) (n : Nat) :
    v13RealLinearSequentialPrefixTranscriptVectorToList
        (v13RealLinearSequentialPrefixTranscriptVectorOf observer
          publicInput n) =
      v13RealLinearSequentialRowPrefixTranscriptOf observer publicInput n := by
  unfold v13RealLinearSequentialPrefixTranscriptVectorToList
  unfold v13RealLinearSequentialPrefixTranscriptVectorOf
  simpa [v13RealLinearSequentialRowPrefixTranscriptOf_length] using
    (List.ofFn_getElem
      (xs :=
        v13RealLinearSequentialRowPrefixTranscriptOf
          observer publicInput n))

theorem v13RealLinearSequentialPrefixTranscriptVectorOf_rows
    {m q : Nat} (observer : V13RealLinearSequentialRowObserver m q)
    (publicInput : V13RealLinearPublic m) (n : Nat) :
    v13RealLinearSequentialPrefixTranscriptVectorRows
        (v13RealLinearSequentialPrefixTranscriptVectorOf observer
          publicInput n) =
      v13RealLinearSequentialRowTranscriptRows
        (v13RealLinearSequentialRowPrefixTranscriptOf
          observer publicInput n) := by
  simp [v13RealLinearSequentialPrefixTranscriptVectorRows,
    v13RealLinearSequentialPrefixTranscriptVectorOf_toList]

theorem v13RealLinearSequentialPrefixTranscriptVectorOf_nextRow
    {m q : Nat} (observer : V13RealLinearSequentialRowObserver m q)
    (publicInput : V13RealLinearPublic m) (n : Nat) :
    v13RealLinearSequentialPrefixTranscriptVectorNextRow observer
        (v13RealLinearSequentialPrefixTranscriptVectorOf observer
          publicInput n) =
      observer.chooseRow
        (v13RealLinearSequentialRowPrefixTranscriptOf
          observer publicInput n) := by
  simp [v13RealLinearSequentialPrefixTranscriptVectorNextRow,
    v13RealLinearSequentialPrefixTranscriptVectorOf_toList]

theorem v13RealLinearSequentialPrefixTranscriptVectorRows_card_le
    {m n : Nat}
    (pref : V13RealLinearSequentialPrefixTranscriptVector m n) :
    (v13RealLinearSequentialPrefixTranscriptVectorRows pref).card ≤ n := by
  simpa [v13RealLinearSequentialPrefixTranscriptVectorRows,
    v13RealLinearSequentialPrefixTranscriptVectorToList] using
    v13RealLinearSequentialRowTranscriptRows_card_le_length
      (v13RealLinearSequentialPrefixTranscriptVectorToList pref)

/-- The ordered RHS-bit history carried by a length-`n` sequential prefix. -/
abbrev V13RealLinearSequentialPrefixRhsHistory (n : Nat) :=
  Fin n → ZMod 2

noncomputable def v13RealLinearSequentialPrefixTranscriptVectorRhs
    {m n : Nat} (pref : V13RealLinearSequentialPrefixTranscriptVector m n) :
    V13RealLinearSequentialPrefixRhsHistory n :=
  fun k => (pref k).2.2

theorem v13RealLinearSequentialPrefixRhsHistory_card (n : Nat) :
    Fintype.card (V13RealLinearSequentialPrefixRhsHistory n) = 2 ^ n := by
  classical
  unfold V13RealLinearSequentialPrefixRhsHistory
  rw [Fintype.card_fun, Fintype.card_fin]
  have hzmod : Fintype.card (ZMod 2) = 2 := by
    norm_num
  rw [hzmod]

theorem v13RealLinearSequentialPrefixTranscriptVectorOf_castSucc
    {m q : Nat} (observer : V13RealLinearSequentialRowObserver m q)
    (publicInput : V13RealLinearPublic m) (n : Nat) (k : Fin n) :
    v13RealLinearSequentialPrefixTranscriptVectorOf observer publicInput
        (n + 1) k.castSucc =
      v13RealLinearSequentialPrefixTranscriptVectorOf observer publicInput
        n k := by
  change
    (v13RealLinearSequentialRowPrefixTranscriptOf observer publicInput
      (n + 1))[k.castSucc]'(by
        simp [v13RealLinearSequentialRowPrefixTranscriptOf_length]) =
    (v13RealLinearSequentialRowPrefixTranscriptOf observer publicInput n)[k]'(by
        simp [v13RealLinearSequentialRowPrefixTranscriptOf_length])
  simp [v13RealLinearSequentialRowPrefixTranscriptOf_succ,
    v13RealLinearSequentialRowPrefixTranscriptOf_length]

theorem v13RealLinearSequentialPrefixTranscriptVectorOf_last
    {m q : Nat} (observer : V13RealLinearSequentialRowObserver m q)
    (publicInput : V13RealLinearPublic m) (n : Nat) :
    v13RealLinearSequentialPrefixTranscriptVectorOf observer publicInput
        (n + 1) ⟨n, Nat.lt_succ_self n⟩ =
      (observer.chooseRow
          (v13RealLinearSequentialRowPrefixTranscriptOf
            observer publicInput n),
        v13RealLinearRowView
          (observer.chooseRow
            (v13RealLinearSequentialRowPrefixTranscriptOf
              observer publicInput n))
          publicInput) := by
  change
    (v13RealLinearSequentialRowPrefixTranscriptOf observer publicInput
      (n + 1))[n]'(by
        simp [v13RealLinearSequentialRowPrefixTranscriptOf_length]) =
      (observer.chooseRow
          (v13RealLinearSequentialRowPrefixTranscriptOf
            observer publicInput n),
        v13RealLinearRowView
          (observer.chooseRow
            (v13RealLinearSequentialRowPrefixTranscriptOf
              observer publicInput n))
          publicInput)
  simp [v13RealLinearSequentialRowPrefixTranscriptOf_succ,
    v13RealLinearSequentialRowPrefixTranscriptOf_length]

theorem v13RealLinearSequentialPrefixTranscriptVectorOf_init
    {m q : Nat} (observer : V13RealLinearSequentialRowObserver m q)
    (publicInput : V13RealLinearPublic m) (n : Nat) :
    v13RealLinearSequentialPrefixTranscriptVectorInit
        (v13RealLinearSequentialPrefixTranscriptVectorOf observer
          publicInput (n + 1)) =
      v13RealLinearSequentialPrefixTranscriptVectorOf observer
        publicInput n := by
  funext k
  exact
    v13RealLinearSequentialPrefixTranscriptVectorOf_castSucc
      observer publicInput n k

theorem v13RealLinearSequentialPrefixTranscriptVectorOf_lastRow
    {m q : Nat} (observer : V13RealLinearSequentialRowObserver m q)
    (publicInput : V13RealLinearPublic m) (n : Nat) :
    v13RealLinearSequentialPrefixTranscriptVectorLastRow
        (v13RealLinearSequentialPrefixTranscriptVectorOf observer
          publicInput (n + 1)) =
      observer.chooseRow
        (v13RealLinearSequentialRowPrefixTranscriptOf
          observer publicInput n) := by
  simp [v13RealLinearSequentialPrefixTranscriptVectorLastRow,
    v13RealLinearSequentialPrefixTranscriptVectorOf_last]

theorem v13RealLinearRowView_eq_of_A_eq_rhs_eq
    {m : Nat} {public₀ public₁ : V13RealLinearPublic m}
    {row : Fin m} (hA : public₀.A = public₁.A)
    (hrhs : public₀.b row = public₁.b row) :
    v13RealLinearRowView row public₀ =
      v13RealLinearRowView row public₁ := by
  rcases public₀ with ⟨A₀, b₀⟩
  rcases public₁ with ⟨A₁, b₁⟩
  dsimp at hA hrhs ⊢
  subst A₁
  exact Prod.ext (by funext probe; rfl) hrhs

theorem
    v13RealLinearSequentialPrefixTranscriptVectorOf_eq_of_A_eq_rhs
    {m q : Nat} (observer : V13RealLinearSequentialRowObserver m q)
    {public₀ public₁ : V13RealLinearPublic m} (n : Nat)
    (hA : public₀.A = public₁.A)
    (hrhs :
      v13RealLinearSequentialPrefixTranscriptVectorRhs
          (v13RealLinearSequentialPrefixTranscriptVectorOf observer
            public₀ n) =
        v13RealLinearSequentialPrefixTranscriptVectorRhs
          (v13RealLinearSequentialPrefixTranscriptVectorOf observer
            public₁ n)) :
    v13RealLinearSequentialPrefixTranscriptVectorOf observer public₀ n =
      v13RealLinearSequentialPrefixTranscriptVectorOf observer public₁ n := by
  induction n with
  | zero =>
      funext k
      exact Fin.elim0 k
  | succ n ih =>
      have hrhsPrev :
          v13RealLinearSequentialPrefixTranscriptVectorRhs
              (v13RealLinearSequentialPrefixTranscriptVectorOf observer
                public₀ n) =
            v13RealLinearSequentialPrefixTranscriptVectorRhs
              (v13RealLinearSequentialPrefixTranscriptVectorOf observer
                public₁ n) := by
        funext k
        have h := congrFun hrhs k.castSucc
        simpa [v13RealLinearSequentialPrefixTranscriptVectorRhs,
          v13RealLinearSequentialPrefixTranscriptVectorOf_castSucc]
          using h
      have hpref := ih hrhsPrev
      have hprefixList :
          v13RealLinearSequentialRowPrefixTranscriptOf
              observer public₀ n =
            v13RealLinearSequentialRowPrefixTranscriptOf
              observer public₁ n := by
        have hlist :=
          congrArg v13RealLinearSequentialPrefixTranscriptVectorToList hpref
        simpa [v13RealLinearSequentialPrefixTranscriptVectorOf_toList]
          using hlist
      funext k
      by_cases hk : (k : Nat) < n
      · let k' : Fin n := ⟨k.1, hk⟩
        have hkEq : k = k'.castSucc := by
          apply Fin.ext
          rfl
        calc
          v13RealLinearSequentialPrefixTranscriptVectorOf observer public₀
              (n + 1) k =
            v13RealLinearSequentialPrefixTranscriptVectorOf observer public₀
              (n + 1) k'.castSucc := by rw [hkEq]
          _ =
            v13RealLinearSequentialPrefixTranscriptVectorOf observer public₀
              n k' :=
            v13RealLinearSequentialPrefixTranscriptVectorOf_castSucc
              observer public₀ n k'
          _ =
            v13RealLinearSequentialPrefixTranscriptVectorOf observer public₁
              n k' := by rw [hpref]
          _ =
            v13RealLinearSequentialPrefixTranscriptVectorOf observer public₁
              (n + 1) k'.castSucc :=
            (v13RealLinearSequentialPrefixTranscriptVectorOf_castSucc
              observer public₁ n k').symm
          _ =
            v13RealLinearSequentialPrefixTranscriptVectorOf observer public₁
              (n + 1) k := by rw [hkEq]
      · have hkLast : k = ⟨n, Nat.lt_succ_self n⟩ := by
          apply Fin.ext
          exact
            le_antisymm
              (Nat.le_of_lt_succ k.2)
              (Nat.le_of_not_gt hk)
        subst k
        have hchoose :
            observer.chooseRow
                (v13RealLinearSequentialRowPrefixTranscriptOf
                  observer public₀ n) =
              observer.chooseRow
                (v13RealLinearSequentialRowPrefixTranscriptOf
                  observer public₁ n) := by
          rw [hprefixList]
        have hrhsLast :
            (v13RealLinearRowView
                (observer.chooseRow
                  (v13RealLinearSequentialRowPrefixTranscriptOf
                    observer public₀ n))
                public₀).2 =
              (v13RealLinearRowView
                (observer.chooseRow
                  (v13RealLinearSequentialRowPrefixTranscriptOf
                    observer public₀ n))
                public₁).2 := by
          have h := congrFun hrhs ⟨n, Nat.lt_succ_self n⟩
          simpa [v13RealLinearSequentialPrefixTranscriptVectorRhs,
            v13RealLinearSequentialPrefixTranscriptVectorOf_last,
            hprefixList] using h
        rw [v13RealLinearSequentialPrefixTranscriptVectorOf_last,
          v13RealLinearSequentialPrefixTranscriptVectorOf_last]
        apply Prod.ext
        · exact hchoose
        · simpa [hchoose] using
            v13RealLinearRowView_eq_of_A_eq_rhs_eq
              hA hrhsLast

noncomputable def
    v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_witness
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t) :
    V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinder
      i₀ observer t activeIdx.1 :=
  Classical.choice activeIdx.2

noncomputable def
    v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedPrefix
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t) :
    V13RealLinearSequentialPrefixTranscriptVector m ((t : Nat) + 1) :=
  let witness :=
    v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_witness
      i₀ observer t activeIdx
  v13RealLinearSequentialPrefixTranscriptVectorOf observer
    (v13RealLinearPublicInput
      ({ x := witness.val, A := activeIdx.1.A.val } : V13RealLinearWorld m))
    ((t : Nat) + 1)

theorem
    v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedPrefix_rows_eq
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t) :
    v13RealLinearSequentialPrefixTranscriptVectorRows
        (v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedPrefix
          i₀ observer t activeIdx) =
      (v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedQBudgetedRowset
        i₀ observer t activeIdx).1 := by
  classical
  let witness :=
    v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_witness
      i₀ observer t activeIdx
  let publicW :=
    v13RealLinearPublicInput
      ({ x := witness.val, A := activeIdx.1.A.val } : V13RealLinearWorld m)
  let traceW :=
    v13RealLinearNoTargetRowsSequentialQRowTrace i₀ observer
      (activeIdx.1.A, witness.val)
  have hlen : (t : Nat) < traceW.length := by
    simpa [traceW] using witness.property.1.1
  have htraceRowsT :
      v13RealLinearRowTracePrefixRows traceW (t : Nat) =
        activeIdx.1.rows := by
    simpa [traceW] using witness.property.2.1
  have hget :
      traceW.get ⟨(t : Nat), hlen⟩ = activeIdx.1.row := by
    rcases witness.property.2.2.1 with ⟨hrowLen, hrowGet⟩
    have hidx :
        (⟨(t : Nat), hlen⟩ : Fin traceW.length) =
          ⟨(t : Nat), by simpa [traceW] using hrowLen⟩ := by
      apply Fin.ext
      rfl
    calc
      traceW.get ⟨(t : Nat), hlen⟩ =
          traceW.get ⟨(t : Nat), by simpa [traceW] using hrowLen⟩ := by
            rw [hidx]
      _ = activeIdx.1.row := by simpa [traceW] using hrowGet
  have htraceRowsSucc :
      v13RealLinearRowTracePrefixRows traceW ((t : Nat) + 1) =
        insert activeIdx.1.row activeIdx.1.rows := by
    rw [v13RealLinearRowTracePrefixRows_succ traceW hlen, hget, htraceRowsT]
  have hseqRows :
      v13RealLinearRowTracePrefixRows traceW ((t : Nat) + 1) =
        v13RealLinearSequentialRowTranscriptRows
          (v13RealLinearSequentialRowPrefixTranscriptOf
            observer publicW ((t : Nat) + 1)) := by
    simpa [traceW, publicW, v13RealLinearNoTargetRowsSequentialQRowTrace]
      using
        v13RealLinearSequentialRowTracePrefixRows_eq_prefixTranscriptRows
          observer publicW (Nat.succ_le_of_lt t.isLt)
  calc
    v13RealLinearSequentialPrefixTranscriptVectorRows
        (v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedPrefix
          i₀ observer t activeIdx) =
      v13RealLinearSequentialRowTranscriptRows
        (v13RealLinearSequentialRowPrefixTranscriptOf
          observer publicW ((t : Nat) + 1)) := by
        simp [
          v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedPrefix,
          witness, publicW,
          v13RealLinearSequentialPrefixTranscriptVectorOf_rows]
    _ = v13RealLinearRowTracePrefixRows traceW ((t : Nat) + 1) := hseqRows.symm
    _ = insert activeIdx.1.row activeIdx.1.rows := htraceRowsSucc
    _ =
      (v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedQBudgetedRowset
        i₀ observer t activeIdx).1 := by
        rfl

theorem
    v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedPrefix_init_rows_eq
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t) :
    v13RealLinearSequentialPrefixTranscriptVectorRows
        (v13RealLinearSequentialPrefixTranscriptVectorInit
          (v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedPrefix
            i₀ observer t activeIdx)) =
      activeIdx.1.rows := by
  classical
  let witness :=
    v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_witness
      i₀ observer t activeIdx
  let publicW :=
    v13RealLinearPublicInput
      ({ x := witness.val, A := activeIdx.1.A.val } : V13RealLinearWorld m)
  let traceW :=
    v13RealLinearNoTargetRowsSequentialQRowTrace i₀ observer
      (activeIdx.1.A, witness.val)
  have htraceRowsT :
      v13RealLinearRowTracePrefixRows traceW (t : Nat) =
        activeIdx.1.rows := by
    simpa [traceW] using witness.property.2.1
  have hseqRows :
      v13RealLinearRowTracePrefixRows traceW (t : Nat) =
        v13RealLinearSequentialRowTranscriptRows
          (v13RealLinearSequentialRowPrefixTranscriptOf
            observer publicW (t : Nat)) := by
    simpa [traceW, publicW, v13RealLinearNoTargetRowsSequentialQRowTrace]
      using
        v13RealLinearSequentialRowTracePrefixRows_eq_prefixTranscriptRows
          observer publicW (Nat.le_of_lt t.isLt)
  calc
    v13RealLinearSequentialPrefixTranscriptVectorRows
        (v13RealLinearSequentialPrefixTranscriptVectorInit
          (v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedPrefix
            i₀ observer t activeIdx)) =
      v13RealLinearSequentialRowTranscriptRows
        (v13RealLinearSequentialRowPrefixTranscriptOf
          observer publicW (t : Nat)) := by
        simp [
          v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedPrefix,
          witness, publicW,
          v13RealLinearSequentialPrefixTranscriptVectorOf_init,
          v13RealLinearSequentialPrefixTranscriptVectorOf_rows]
    _ = v13RealLinearRowTracePrefixRows traceW (t : Nat) := hseqRows.symm
    _ = activeIdx.1.rows := htraceRowsT

theorem
    v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedPrefix_lastRow_eq
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t) :
    v13RealLinearSequentialPrefixTranscriptVectorLastRow
        (v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedPrefix
          i₀ observer t activeIdx) =
      activeIdx.1.row := by
  classical
  let witness :=
    v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_witness
      i₀ observer t activeIdx
  let publicW :=
    v13RealLinearPublicInput
      ({ x := witness.val, A := activeIdx.1.A.val } : V13RealLinearWorld m)
  let traceW :=
    v13RealLinearNoTargetRowsSequentialQRowTrace i₀ observer
      (activeIdx.1.A, witness.val)
  have hlen : (t : Nat) < traceW.length := by
    simpa [traceW] using witness.property.1.1
  have hget :
      traceW.get ⟨(t : Nat), hlen⟩ = activeIdx.1.row := by
    rcases witness.property.2.2.1 with ⟨hrowLen, hrowGet⟩
    have hidx :
        (⟨(t : Nat), hlen⟩ : Fin traceW.length) =
          ⟨(t : Nat), by simpa [traceW] using hrowLen⟩ := by
      apply Fin.ext
      rfl
    calc
      traceW.get ⟨(t : Nat), hlen⟩ =
          traceW.get ⟨(t : Nat), by simpa [traceW] using hrowLen⟩ := by
            rw [hidx]
      _ = activeIdx.1.row := by simpa [traceW] using hrowGet
  have hchoose :
      traceW.get ⟨(t : Nat), hlen⟩ =
        observer.chooseRow
          (v13RealLinearSequentialRowPrefixTranscriptOf
            observer publicW (t : Nat)) := by
    simpa [traceW, publicW, v13RealLinearNoTargetRowsSequentialQRowTrace]
      using
        v13RealLinearSequentialRowTraceOf_get_eq_chooseRow
          observer publicW t.isLt
  calc
    v13RealLinearSequentialPrefixTranscriptVectorLastRow
        (v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedPrefix
          i₀ observer t activeIdx) =
      observer.chooseRow
        (v13RealLinearSequentialRowPrefixTranscriptOf
          observer publicW (t : Nat)) := by
        simp [
          v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedPrefix,
          witness, publicW,
          v13RealLinearSequentialPrefixTranscriptVectorOf_lastRow]
    _ = traceW.get ⟨(t : Nat), hlen⟩ := hchoose.symm
    _ = activeIdx.1.row := hget

theorem
    v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex_eq_of_sameMap_generatedPrefix
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (activeIdx₀ activeIdx₁ :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t)
    (hA : activeIdx₀.1.A = activeIdx₁.1.A)
    (hpref :
      v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedPrefix
          i₀ observer t activeIdx₀ =
        v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedPrefix
          i₀ observer t activeIdx₁) :
    activeIdx₀ = activeIdx₁ := by
  classical
  let witness₀ :=
    v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_witness
      i₀ observer t activeIdx₀
  let witness₁ :=
    v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_witness
      i₀ observer t activeIdx₁
  let public₀ :=
    v13RealLinearPublicInput
      ({ x := witness₀.val, A := activeIdx₀.1.A.val } :
        V13RealLinearWorld m)
  let public₁ :=
    v13RealLinearPublicInput
      ({ x := witness₁.val, A := activeIdx₁.1.A.val } :
        V13RealLinearWorld m)
  have hinitVec :
      v13RealLinearSequentialPrefixTranscriptVectorInit
          (v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedPrefix
            i₀ observer t activeIdx₀) =
        v13RealLinearSequentialPrefixTranscriptVectorInit
          (v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedPrefix
            i₀ observer t activeIdx₁) := by
    exact congrArg
      (fun pref :
        V13RealLinearSequentialPrefixTranscriptVector m ((t : Nat) + 1) =>
        v13RealLinearSequentialPrefixTranscriptVectorInit pref)
      hpref
  have hrows :
      activeIdx₀.1.rows = activeIdx₁.1.rows := by
    have hrowsVec :=
      congrArg v13RealLinearSequentialPrefixTranscriptVectorRows hinitVec
    simpa [
      v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedPrefix_init_rows_eq]
      using hrowsVec
  have hrow :
      activeIdx₀.1.row = activeIdx₁.1.row := by
    have hlast :=
      congrArg v13RealLinearSequentialPrefixTranscriptVectorLastRow hpref
    simpa [
      v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedPrefix_lastRow_eq]
      using hlast
  have hprefixList :
      v13RealLinearSequentialRowPrefixTranscriptOf
          observer public₀ (t : Nat) =
        v13RealLinearSequentialRowPrefixTranscriptOf
          observer public₁ (t : Nat) := by
    have hlist :=
      congrArg v13RealLinearSequentialPrefixTranscriptVectorToList hinitVec
    simpa [
      v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedPrefix,
      witness₀, witness₁, public₀, public₁,
      v13RealLinearSequentialPrefixTranscriptVectorOf_init,
      v13RealLinearSequentialPrefixTranscriptVectorOf_toList]
      using hlist
  have hprefixRows₀ :
      v13RealLinearSequentialRowTranscriptRows
          (v13RealLinearSequentialRowPrefixTranscriptOf
            observer public₀ (t : Nat)) =
        activeIdx₀.1.rows := by
    have hinitRows :=
      v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedPrefix_init_rows_eq
        i₀ observer t activeIdx₀
    simpa [
      v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedPrefix,
      witness₀, public₀,
      v13RealLinearSequentialPrefixTranscriptVectorOf_init,
      v13RealLinearSequentialPrefixTranscriptVectorOf_rows]
      using hinitRows
  have hrowsTranscript :
      v13RealLinearRowsTranscript activeIdx₀.1.rows public₀ =
        v13RealLinearRowsTranscript activeIdx₀.1.rows public₁ := by
    have hprefixTranscript :=
      v13RealLinearRowsTranscript_eq_of_sequentialPrefixTranscript_eq
        observer public₀ public₁ (t : Nat) hprefixList
    rw [hprefixRows₀] at hprefixTranscript
    exact hprefixTranscript
  have htranscript₀ :
      v13RealLinearRowsTranscript activeIdx₀.1.rows public₀ =
        activeIdx₀.1.transcript := by
    simpa [witness₀, public₀] using witness₀.property.2.2.2
  have htranscript₁ :
      v13RealLinearRowsTranscript activeIdx₁.1.rows public₁ =
        activeIdx₁.1.transcript := by
    simpa [witness₁, public₁] using witness₁.property.2.2.2
  apply Subtype.ext
  cases activeIdx₀ with
  | mk idx₀ hactive₀ =>
      cases activeIdx₁ with
      | mk idx₁ hactive₁ =>
          dsimp at hA hrows hrow htranscript₀ htranscript₁ hrowsTranscript ⊢
          cases idx₀ with
          | mk A₀ rows₀ row₀ hit₀ transcript₀ =>
              cases idx₁ with
              | mk A₁ rows₁ row₁ hit₁ transcript₁ =>
                  dsimp at hA hrows hrow htranscript₀ htranscript₁ hrowsTranscript ⊢
                  subst A₁
                  subst rows₁
                  subst row₁
                  have htranscript :
                      transcript₀ = transcript₁ := by
                    calc
                      transcript₀ =
                          v13RealLinearRowsTranscript rows₀ public₀ :=
                        htranscript₀.symm
                      _ = v13RealLinearRowsTranscript rows₀ public₁ :=
                        hrowsTranscript
                      _ = transcript₁ := htranscript₁
                  clear hpref hinitVec hprefixList hprefixRows₀
                  clear hrowsTranscript htranscript₀ htranscript₁
                  clear witness₀ witness₁ public₀ public₁ hactive₀ hactive₁
                  subst transcript₁
                  have hhit : hit₀ = hit₁ := Subsingleton.elim _ _
                  subst hit₁
                  rfl

theorem
    v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedPrefix_eq_of_sameMap_rhs
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (activeIdx₀ activeIdx₁ :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t)
    (hA : activeIdx₀.1.A = activeIdx₁.1.A)
    (hrhs :
      v13RealLinearSequentialPrefixTranscriptVectorRhs
          (v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedPrefix
            i₀ observer t activeIdx₀) =
        v13RealLinearSequentialPrefixTranscriptVectorRhs
          (v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedPrefix
            i₀ observer t activeIdx₁)) :
    v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedPrefix
        i₀ observer t activeIdx₀ =
      v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedPrefix
        i₀ observer t activeIdx₁ := by
  classical
  unfold
    v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedPrefix
  apply
    v13RealLinearSequentialPrefixTranscriptVectorOf_eq_of_A_eq_rhs
      observer ((t : Nat) + 1)
  · simpa [v13RealLinearPublicInput] using congrArg Subtype.val hA
  · simpa [
      v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedPrefix]
      using hrhs

abbrev
    V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveGeneratedPrefixForMap
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (A : V13RealLinearNoTargetRowsMap m i₀) :=
  {pref : V13RealLinearSequentialPrefixTranscriptVector m ((t : Nat) + 1) //
    ∃ activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t,
      activeIdx.1.A = A ∧
        v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedPrefix
          i₀ observer t activeIdx = pref}

noncomputable instance
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (A : V13RealLinearNoTargetRowsMap m i₀) :
    Fintype
      (V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveGeneratedPrefixForMap
        i₀ observer t A) := by
  classical
  unfold
    V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveGeneratedPrefixForMap
  infer_instance

noncomputable def
    v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveGeneratedPrefixForMapToRhsHistory
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (A : V13RealLinearNoTargetRowsMap m i₀) :
    V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveGeneratedPrefixForMap
        i₀ observer t A ↪
      V13RealLinearSequentialPrefixRhsHistory ((t : Nat) + 1) where
  toFun pref := v13RealLinearSequentialPrefixTranscriptVectorRhs pref.val
  inj' := by
    classical
    intro pref₀ pref₁ hrhs
    apply Subtype.ext
    rcases pref₀.property with ⟨activeIdx₀, hA₀, hpref₀⟩
    rcases pref₁.property with ⟨activeIdx₁, hA₁, hpref₁⟩
    have hA : activeIdx₀.1.A = activeIdx₁.1.A := hA₀.trans hA₁.symm
    have hprefix :=
      v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedPrefix_eq_of_sameMap_rhs
        i₀ observer t activeIdx₀ activeIdx₁ hA
        (by
          simpa [hpref₀, hpref₁] using hrhs)
    exact hpref₀ ▸ hpref₁ ▸ hprefix

theorem
    v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveGeneratedPrefixForMap_card_le_rhsHistory
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (A : V13RealLinearNoTargetRowsMap m i₀) :
    Fintype.card
        (V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveGeneratedPrefixForMap
          i₀ observer t A) ≤
      2 ^ ((t : Nat) + 1) := by
  classical
  calc
    Fintype.card
        (V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveGeneratedPrefixForMap
          i₀ observer t A) ≤
      Fintype.card
        (V13RealLinearSequentialPrefixRhsHistory ((t : Nat) + 1)) :=
        Fintype.card_le_of_embedding
          (v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveGeneratedPrefixForMapToRhsHistory
            i₀ observer t A)
    _ = 2 ^ ((t : Nat) + 1) :=
        v13RealLinearSequentialPrefixRhsHistory_card ((t : Nat) + 1)

abbrev
    V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndexForMap
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (A : V13RealLinearNoTargetRowsMap m i₀) :=
  {activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t //
    activeIdx.1.A = A}

noncomputable instance
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (A : V13RealLinearNoTargetRowsMap m i₀) :
    Fintype
      (V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndexForMap
        i₀ observer t A) := by
  classical
  unfold
    V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndexForMap
  infer_instance

noncomputable def
    v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndexForMapToGeneratedPrefixForMap
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (A : V13RealLinearNoTargetRowsMap m i₀) :
    V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndexForMap
        i₀ observer t A ↪
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveGeneratedPrefixForMap
        i₀ observer t A where
  toFun activeIdx :=
    ⟨v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedPrefix
        i₀ observer t activeIdx.val,
      ⟨activeIdx.val, activeIdx.property, rfl⟩⟩
  inj' := by
    intro activeIdx₀ activeIdx₁ hpref
    apply Subtype.ext
    exact
      v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex_eq_of_sameMap_generatedPrefix
        i₀ observer t activeIdx₀.val activeIdx₁.val
        (activeIdx₀.property.trans activeIdx₁.property.symm)
        (congrArg Subtype.val hpref)

theorem
    v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndexForMap_card_le_rhsHistory
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (A : V13RealLinearNoTargetRowsMap m i₀) :
    Fintype.card
        (V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndexForMap
          i₀ observer t A) ≤
      2 ^ ((t : Nat) + 1) := by
  classical
  calc
    Fintype.card
        (V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndexForMap
          i₀ observer t A) ≤
      Fintype.card
        (V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveGeneratedPrefixForMap
          i₀ observer t A) :=
        Fintype.card_le_of_embedding
          (v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndexForMapToGeneratedPrefixForMap
            i₀ observer t A)
    _ ≤ 2 ^ ((t : Nat) + 1) :=
        v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveGeneratedPrefixForMap_card_le_rhsHistory
          i₀ observer t A

noncomputable def
    v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedTranscript
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t) :
    V13RealLinearRowsTranscriptSpace m
      (v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedQBudgetedRowset
        i₀ observer t activeIdx).1 :=
  let witness :=
    v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_witness
      i₀ observer t activeIdx
  v13RealLinearRowsTranscript
    (v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedQBudgetedRowset
      i₀ observer t activeIdx).1
    (v13RealLinearPublicInput
      ({ x := witness.val, A := activeIdx.1.A.val } : V13RealLinearWorld m))

abbrev
    V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderGeneratedPrefixCell
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t) :=
  {x : F2Vec m //
    v13RealLinearSequentialPrefixTranscriptVectorOf observer
        (v13RealLinearPublicInput
          ({ x := x, A := activeIdx.1.A.val } : V13RealLinearWorld m))
        ((t : Nat) + 1) =
      v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedPrefix
        i₀ observer t activeIdx ∧
    v13RealLinearRowsTranscript
        (v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedQBudgetedRowset
          i₀ observer t activeIdx).1
        (v13RealLinearPublicInput
          ({ x := x, A := activeIdx.1.A.val } : V13RealLinearWorld m)) =
      v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedTranscript
        i₀ observer t activeIdx}

noncomputable instance
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t) :
    Fintype
      (V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderGeneratedPrefixCell
        i₀ observer t activeIdx) := by
  classical
  unfold
    V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderGeneratedPrefixCell
  infer_instance

theorem
    v13RealLinearNoTargetSequentialTraceFirstCosetHitGeneratedPrefixCell_rhs_eq
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t)
    (cell :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderGeneratedPrefixCell
        i₀ observer t activeIdx) :
    v13RealLinearSequentialPrefixTranscriptVectorRhs
        (v13RealLinearSequentialPrefixTranscriptVectorOf observer
          (v13RealLinearPublicInput
            ({ x := cell.val, A := activeIdx.1.A.val } :
              V13RealLinearWorld m))
          ((t : Nat) + 1)) =
      v13RealLinearSequentialPrefixTranscriptVectorRhs
        (v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedPrefix
          i₀ observer t activeIdx) := by
  exact congrArg v13RealLinearSequentialPrefixTranscriptVectorRhs cell.property.1

noncomputable def
    v13RealLinearRowsUnreadAssignmentToActiveNoTargetSequentialTraceFirstCosetHitGeneratedPrefixCell
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t) :
    V13RealLinearRowsUnreadAssignment m
        (v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedQBudgetedRowset
          i₀ observer t activeIdx).1 ↪
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderGeneratedPrefixCell
        i₀ observer t activeIdx where
  toFun assignment := by
    classical
    let witness :=
      v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_witness
        i₀ observer t activeIdx
    let G :=
      (v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedQBudgetedRowset
        i₀ observer t activeIdx).1
    let transcript :=
      v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedTranscript
        i₀ observer t activeIdx
    let publicW :=
      v13RealLinearPublicInput
        ({ x := witness.val, A := activeIdx.1.A.val } : V13RealLinearWorld m)
    let b : F2Vec m :=
      v13RealLinearRowsTranscriptCompletion transcript assignment
    let z : F2Vec m := activeIdx.1.A.val.toEquiv.symm b
    let publicZ :=
      v13RealLinearPublicInput
        ({ x := z, A := activeIdx.1.A.val } : V13RealLinearWorld m)
    have htranscriptZ :
        v13RealLinearRowsTranscript G publicZ = transcript := by
      funext row
      apply Prod.ext
      · funext probe
        rfl
      · change activeIdx.1.A.val.toEquiv z row.1 = (transcript row).2
        calc
          activeIdx.1.A.val.toEquiv z row.1 =
              v13RealLinearRowsTranscriptCompletion transcript assignment row.1 := by
            simp [z, b]
          _ = (transcript row).2 :=
            v13RealLinearRowsTranscriptCompletion_of_mem
              transcript assignment row.property
    have hsameG :
        v13RealLinearRowsTranscript G publicW =
          v13RealLinearRowsTranscript G publicZ := by
      rw [htranscriptZ]
      rfl
    have hprefixRowsW :
        v13RealLinearSequentialRowTranscriptRows
            (v13RealLinearSequentialRowPrefixTranscriptOf
              observer publicW ((t : Nat) + 1)) =
          G := by
      have hrows :=
        v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedPrefix_rows_eq
          i₀ observer t activeIdx
      simpa [
        v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedPrefix,
        witness, publicW, G,
        v13RealLinearSequentialPrefixTranscriptVectorOf_rows] using hrows
    have hsameRows :
        v13RealLinearRowsTranscript
            (v13RealLinearSequentialRowTranscriptRows
              (v13RealLinearSequentialRowPrefixTranscriptOf
                observer publicW ((t : Nat) + 1))) publicW =
          v13RealLinearRowsTranscript
            (v13RealLinearSequentialRowTranscriptRows
              (v13RealLinearSequentialRowPrefixTranscriptOf
                observer publicW ((t : Nat) + 1))) publicZ := by
      rw [hprefixRowsW]
      exact hsameG
    have hprefixTranscript :
        v13RealLinearSequentialRowPrefixTranscriptOf
            observer publicZ ((t : Nat) + 1) =
          v13RealLinearSequentialRowPrefixTranscriptOf
            observer publicW ((t : Nat) + 1) := by
      simpa [v13RealLinearSequentialRowPrefixTranscriptOf] using
        v13RealLinearSequentialRowRunAux_eq_of_final_rowsTranscript_eq
          observer publicW publicZ ((t : Nat) + 1) [] hsameRows
    exact
      ⟨z, by
        have hlist :
            v13RealLinearSequentialPrefixTranscriptVectorToList
                (v13RealLinearSequentialPrefixTranscriptVectorOf observer
                  publicZ ((t : Nat) + 1)) =
              v13RealLinearSequentialPrefixTranscriptVectorToList
                (v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedPrefix
                  i₀ observer t activeIdx) := by
          simpa [
            v13RealLinearSequentialPrefixTranscriptVectorOf_toList,
            v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedPrefix,
            witness, publicW, publicZ] using hprefixTranscript
        exact ⟨List.ofFn_inj.mp (by
          simpa [
            v13RealLinearSequentialPrefixTranscriptVectorToList,
            v13RealLinearSequentialPrefixTranscriptVectorOf,
            v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedPrefix,
            witness, publicW, publicZ] using hlist), htranscriptZ⟩⟩
  inj' := by
    classical
    intro assignment₀ assignment₁ hcell
    let G :=
      (v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedQBudgetedRowset
        i₀ observer t activeIdx).1
    let transcript :=
      v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedTranscript
        i₀ observer t activeIdx
    let complete : V13RealLinearRowsUnreadAssignment m G → F2Vec m :=
      fun assignment =>
        activeIdx.1.A.val.toEquiv.symm
          (v13RealLinearRowsTranscriptCompletion transcript assignment)
    have hz : complete assignment₀ = complete assignment₁ := by
      simpa [complete, G, transcript] using
        congrArg
          (fun cell :
            V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderGeneratedPrefixCell
              i₀ observer t activeIdx => cell.val)
          hcell
    funext row
    have hAraw :=
      congrFun (congrArg activeIdx.1.A.val.toEquiv hz) row.1
    have hA :
        v13RealLinearRowsTranscriptCompletion transcript assignment₀ row.1 =
          v13RealLinearRowsTranscriptCompletion transcript assignment₁ row.1 := by
      simpa [complete] using hAraw
    calc
      assignment₀ row =
          v13RealLinearRowsTranscriptCompletion transcript assignment₀ row.1 := by
        exact
          (v13RealLinearRowsTranscriptCompletion_of_not_mem
            transcript assignment₀ row).symm
      _ =
          v13RealLinearRowsTranscriptCompletion transcript assignment₁ row.1 := hA
      _ = assignment₁ row :=
          v13RealLinearRowsTranscriptCompletion_of_not_mem
            transcript assignment₁ row

theorem
    v13RealLinearNoTargetSequentialTraceFirstCosetHitGeneratedPrefixCell_capacity_le_card
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t) :
    2 ^ (m -
        (v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedQBudgetedRowset
          i₀ observer t activeIdx).1.card) ≤
      Fintype.card
        (V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderGeneratedPrefixCell
          i₀ observer t activeIdx) := by
  classical
  have hle :
      Fintype.card
          (V13RealLinearRowsUnreadAssignment m
            (v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedQBudgetedRowset
              i₀ observer t activeIdx).1) ≤
        Fintype.card
          (V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderGeneratedPrefixCell
            i₀ observer t activeIdx) :=
    Fintype.card_le_of_embedding
      (v13RealLinearRowsUnreadAssignmentToActiveNoTargetSequentialTraceFirstCosetHitGeneratedPrefixCell
        i₀ observer t activeIdx)
  simpa [v13RealLinearRowsUnreadAssignment_card] using hle

noncomputable def
    v13RealLinearNoTargetSequentialTraceFirstCosetHitGeneratedPrefixCellToUnreadAssignment
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t) :
    V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderGeneratedPrefixCell
        i₀ observer t activeIdx ↪
      V13RealLinearRowsUnreadAssignment m
        (v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedQBudgetedRowset
          i₀ observer t activeIdx).1 where
  toFun cell := fun unread => activeIdx.1.A.val.toEquiv cell.val unread.1
  inj' := by
    classical
    intro cell₀ cell₁ hassign
    apply Subtype.ext
    apply activeIdx.1.A.val.toEquiv.injective
    funext row
    let G :=
      (v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedQBudgetedRowset
        i₀ observer t activeIdx).1
    by_cases hrow : row ∈ G
    · have htranscript :
          v13RealLinearRowsTranscript G
              (v13RealLinearPublicInput
                ({ x := cell₀.val, A := activeIdx.1.A.val } :
                  V13RealLinearWorld m)) =
            v13RealLinearRowsTranscript G
              (v13RealLinearPublicInput
                ({ x := cell₁.val, A := activeIdx.1.A.val } :
                  V13RealLinearWorld m)) := by
        exact cell₀.property.2.trans cell₁.property.2.symm
      have hview := congrFun htranscript ⟨row, hrow⟩
      simpa [G, v13RealLinearRowsTranscript, v13RealLinearRowView,
        v13RealLinearPublicInput] using congrArg Prod.snd hview
    · exact congrFun hassign ⟨row, hrow⟩

theorem
    v13RealLinearNoTargetSequentialTraceFirstCosetHitGeneratedPrefixCell_card_le_capacity
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t) :
    Fintype.card
        (V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderGeneratedPrefixCell
          i₀ observer t activeIdx) ≤
      2 ^ (m -
        (v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedQBudgetedRowset
          i₀ observer t activeIdx).1.card) := by
  classical
  have hle :
      Fintype.card
          (V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderGeneratedPrefixCell
            i₀ observer t activeIdx) ≤
        Fintype.card
          (V13RealLinearRowsUnreadAssignment m
            (v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedQBudgetedRowset
              i₀ observer t activeIdx).1) :=
    Fintype.card_le_of_embedding
      (v13RealLinearNoTargetSequentialTraceFirstCosetHitGeneratedPrefixCellToUnreadAssignment
        i₀ observer t activeIdx)
  exact hle.trans_eq
    (v13RealLinearRowsUnreadAssignment_card
      (v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedQBudgetedRowset
        i₀ observer t activeIdx).1)

theorem
    v13RealLinearNoTargetSequentialTraceFirstCosetHitGeneratedPrefixCell_card_eq_capacity
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t) :
    Fintype.card
        (V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderGeneratedPrefixCell
          i₀ observer t activeIdx) =
      2 ^ (m -
        (v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedQBudgetedRowset
          i₀ observer t activeIdx).1.card) := by
  exact
    le_antisymm
      (v13RealLinearNoTargetSequentialTraceFirstCosetHitGeneratedPrefixCell_card_le_capacity
        i₀ observer t activeIdx)
      (v13RealLinearNoTargetSequentialTraceFirstCosetHitGeneratedPrefixCell_capacity_le_card
        i₀ observer t activeIdx)

abbrev
    V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveGeneratedPrefixCellIndexForWorld
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (omega :
      V13RealLinearAdaptiveQRowWorld m
        (V13RealLinearNoTargetRowsMap m i₀)) :=
  {activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t //
    activeIdx.1.A = omega.1 ∧
      ∃ cell :
        V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderGeneratedPrefixCell
          i₀ observer t activeIdx,
        cell.val = omega.2}

noncomputable instance
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (omega :
      V13RealLinearAdaptiveQRowWorld m
        (V13RealLinearNoTargetRowsMap m i₀)) :
    Fintype
      (V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveGeneratedPrefixCellIndexForWorld
        i₀ observer t omega) := by
  classical
  unfold
    V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveGeneratedPrefixCellIndexForWorld
  infer_instance

noncomputable def
    v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveGeneratedPrefixCellIndexForWorldToIndexForMap
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (omega :
      V13RealLinearAdaptiveQRowWorld m
        (V13RealLinearNoTargetRowsMap m i₀)) :
    V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveGeneratedPrefixCellIndexForWorld
        i₀ observer t omega ↪
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndexForMap
        i₀ observer t omega.1 where
  toFun activeIdx := ⟨activeIdx.val, activeIdx.property.1⟩
  inj' := by
    intro activeIdx₀ activeIdx₁ h
    apply Subtype.ext
    exact
      congrArg
        (fun activeIdx :
          V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndexForMap
            i₀ observer t omega.1 => activeIdx.val)
        h

theorem
    v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveGeneratedPrefixCellIndexForWorld_card_le_rhsHistory
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (omega :
      V13RealLinearAdaptiveQRowWorld m
        (V13RealLinearNoTargetRowsMap m i₀)) :
    Fintype.card
        (V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveGeneratedPrefixCellIndexForWorld
          i₀ observer t omega) ≤
      2 ^ ((t : Nat) + 1) := by
  classical
  calc
    Fintype.card
        (V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveGeneratedPrefixCellIndexForWorld
          i₀ observer t omega) ≤
      Fintype.card
        (V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndexForMap
          i₀ observer t omega.1) :=
        Fintype.card_le_of_embedding
          (v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveGeneratedPrefixCellIndexForWorldToIndexForMap
            i₀ observer t omega)
    _ ≤ 2 ^ ((t : Nat) + 1) :=
        v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndexForMap_card_le_rhsHistory
          i₀ observer t omega.1

theorem
    v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveGeneratedPrefixCellIndexForWorld_subsingleton
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (omega :
      V13RealLinearAdaptiveQRowWorld m
        (V13RealLinearNoTargetRowsMap m i₀)) :
    Subsingleton
      (V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveGeneratedPrefixCellIndexForWorld
        i₀ observer t omega) := by
  classical
  refine ⟨?_⟩
  intro activeIdx₀ activeIdx₁
  rcases activeIdx₀.property with ⟨hA₀, hcell₀⟩
  rcases activeIdx₁.property with ⟨hA₁, hcell₁⟩
  rcases hcell₀ with ⟨cell₀, hcellVal₀⟩
  rcases hcell₁ with ⟨cell₁, hcellVal₁⟩
  have hA : activeIdx₀.val.1.A = activeIdx₁.val.1.A := hA₀.trans hA₁.symm
  have hpref :
      v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedPrefix
          i₀ observer t activeIdx₀.val =
        v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedPrefix
          i₀ observer t activeIdx₁.val := by
    calc
      v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedPrefix
          i₀ observer t activeIdx₀.val =
        v13RealLinearSequentialPrefixTranscriptVectorOf observer
          (v13RealLinearPublicInput
            ({ x := omega.2, A := activeIdx₀.val.1.A.val } :
              V13RealLinearWorld m))
          ((t : Nat) + 1) := by
          rw [← cell₀.property.1, hcellVal₀]
      _ =
        v13RealLinearSequentialPrefixTranscriptVectorOf observer
          (v13RealLinearPublicInput
            ({ x := omega.2, A := omega.1.val } :
              V13RealLinearWorld m))
          ((t : Nat) + 1) := by
          rw [hA₀]
      _ =
        v13RealLinearSequentialPrefixTranscriptVectorOf observer
          (v13RealLinearPublicInput
            ({ x := omega.2, A := activeIdx₁.val.1.A.val } :
              V13RealLinearWorld m))
          ((t : Nat) + 1) := by
          rw [hA₁]
      _ =
        v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedPrefix
          i₀ observer t activeIdx₁.val := by
          rw [← cell₁.property.1, hcellVal₁]
  apply Subtype.ext
  exact
    v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex_eq_of_sameMap_generatedPrefix
      i₀ observer t activeIdx₀.val activeIdx₁.val hA hpref

theorem
    v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveGeneratedPrefixCellIndexForWorld_card_le_one
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (omega :
      V13RealLinearAdaptiveQRowWorld m
        (V13RealLinearNoTargetRowsMap m i₀)) :
    Fintype.card
        (V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveGeneratedPrefixCellIndexForWorld
          i₀ observer t omega) ≤
      1 := by
  classical
  letI :=
    v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveGeneratedPrefixCellIndexForWorld_subsingleton
      i₀ observer t omega
  exact Fintype.card_le_one_iff_subsingleton.mpr inferInstance

noncomputable def
    v13RealLinearNoTargetSequentialTraceFirstCosetHitGeneratedPrefixCellToFixedMapTranscriptCylinder
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t) :
    V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderGeneratedPrefixCell
        i₀ observer t activeIdx ↪
      V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinder
        i₀ observer t activeIdx.1 where
  toFun cell := by
    classical
    let idx := activeIdx.1
    let witness :=
      v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_witness
        i₀ observer t activeIdx
    let publicW :=
      v13RealLinearPublicInput
        ({ x := witness.val, A := idx.A.val } : V13RealLinearWorld m)
    let publicZ :=
      v13RealLinearPublicInput
        ({ x := cell.val, A := idx.A.val } : V13RealLinearWorld m)
    let traceW :=
      v13RealLinearNoTargetRowsSequentialQRowTrace i₀ observer
        (idx.A, witness.val)
    let traceZ :=
      v13RealLinearNoTargetRowsSequentialQRowTrace i₀ observer
        (idx.A, cell.val)
    let G :=
      (v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedQBudgetedRowset
        i₀ observer t activeIdx).1
    have hprefixSucc :
        v13RealLinearSequentialRowPrefixTranscriptOf
            observer publicZ ((t : Nat) + 1) =
          v13RealLinearSequentialRowPrefixTranscriptOf
            observer publicW ((t : Nat) + 1) := by
      have hlist :
          v13RealLinearSequentialPrefixTranscriptVectorToList
              (v13RealLinearSequentialPrefixTranscriptVectorOf observer
                publicZ ((t : Nat) + 1)) =
            v13RealLinearSequentialPrefixTranscriptVectorToList
              (v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedPrefix
                i₀ observer t activeIdx) := by
        exact congrArg v13RealLinearSequentialPrefixTranscriptVectorToList
          cell.property.1
      simpa [
        v13RealLinearSequentialPrefixTranscriptVectorOf_toList,
        v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedPrefix,
        witness, publicW, publicZ] using hlist
    have hprefixT :
        v13RealLinearSequentialRowPrefixTranscriptOf
            observer publicZ (t : Nat) =
          v13RealLinearSequentialRowPrefixTranscriptOf
            observer publicW (t : Nat) := by
      have htake :=
        congrArg (fun transcript :
            V13RealLinearSequentialRowTranscript m =>
          transcript.take (t : Nat)) hprefixSucc
      simpa [v13RealLinearSequentialRowPrefixTranscriptOf_succ,
        v13RealLinearSequentialRowPrefixTranscriptOf_length] using htake
    have htraceRowsZ :
        v13RealLinearRowTracePrefixRows traceZ (t : Nat) = idx.rows := by
      have htraceToTranscriptZ :
          v13RealLinearRowTracePrefixRows traceZ (t : Nat) =
            v13RealLinearSequentialRowTranscriptRows
              (v13RealLinearSequentialRowPrefixTranscriptOf
                observer publicZ (t : Nat)) := by
        simpa [traceZ, publicZ,
          v13RealLinearNoTargetRowsSequentialQRowTrace] using
          v13RealLinearSequentialRowTracePrefixRows_eq_prefixTranscriptRows
            observer publicZ (Nat.le_of_lt t.isLt)
      have htraceToTranscriptW :
          v13RealLinearRowTracePrefixRows traceW (t : Nat) =
            v13RealLinearSequentialRowTranscriptRows
              (v13RealLinearSequentialRowPrefixTranscriptOf
                observer publicW (t : Nat)) := by
        simpa [traceW, publicW,
          v13RealLinearNoTargetRowsSequentialQRowTrace] using
          v13RealLinearSequentialRowTracePrefixRows_eq_prefixTranscriptRows
            observer publicW (Nat.le_of_lt t.isLt)
      have hrowsW :
          v13RealLinearRowTracePrefixRows traceW (t : Nat) = idx.rows := by
        simpa [traceW, idx] using witness.property.2.1
      calc
        v13RealLinearRowTracePrefixRows traceZ (t : Nat) =
            v13RealLinearSequentialRowTranscriptRows
              (v13RealLinearSequentialRowPrefixTranscriptOf
                observer publicZ (t : Nat)) := htraceToTranscriptZ
        _ =
            v13RealLinearSequentialRowTranscriptRows
              (v13RealLinearSequentialRowPrefixTranscriptOf
                observer publicW (t : Nat)) := by rw [hprefixT]
        _ = v13RealLinearRowTracePrefixRows traceW (t : Nat) :=
            htraceToTranscriptW.symm
        _ = idx.rows := hrowsW
    have hlenZ : (t : Nat) < traceZ.length := by
      simp [traceZ, v13RealLinearNoTargetRowsSequentialQRowTrace,
        v13RealLinearSequentialRowTraceOf_length]
    have hgetZ :
        traceZ.get ⟨(t : Nat), hlenZ⟩ = idx.row := by
      rcases witness.property.2.2.1 with ⟨hlenWCell, hgetWCell⟩
      have hlenW : (t : Nat) < traceW.length := by
        simp [traceW, v13RealLinearNoTargetRowsSequentialQRowTrace,
          v13RealLinearSequentialRowTraceOf_length]
      have hchooseZ :
          traceZ.get ⟨(t : Nat), hlenZ⟩ =
            observer.chooseRow
              (v13RealLinearSequentialRowPrefixTranscriptOf
                observer publicZ (t : Nat)) := by
        simpa [traceZ, publicZ,
          v13RealLinearNoTargetRowsSequentialQRowTrace] using
          v13RealLinearSequentialRowTraceOf_get_eq_chooseRow
            observer publicZ t.isLt
      have hchooseW :
          traceW.get ⟨(t : Nat), hlenW⟩ =
            observer.chooseRow
              (v13RealLinearSequentialRowPrefixTranscriptOf
                observer publicW (t : Nat)) := by
        simpa [traceW, publicW,
          v13RealLinearNoTargetRowsSequentialQRowTrace] using
          v13RealLinearSequentialRowTraceOf_get_eq_chooseRow
            observer publicW t.isLt
      have hidxW :
          (⟨(t : Nat), hlenW⟩ : Fin traceW.length) =
            ⟨(t : Nat), by simpa [traceW] using hlenWCell⟩ := by
        apply Fin.ext
        rfl
      calc
        traceZ.get ⟨(t : Nat), hlenZ⟩ =
            observer.chooseRow
              (v13RealLinearSequentialRowPrefixTranscriptOf
                observer publicZ (t : Nat)) := hchooseZ
        _ =
            observer.chooseRow
              (v13RealLinearSequentialRowPrefixTranscriptOf
                observer publicW (t : Nat)) := by rw [hprefixT]
        _ = traceW.get ⟨(t : Nat), hlenW⟩ := hchooseW.symm
        _ = traceW.get
            ⟨(t : Nat), by simpa [traceW] using hlenWCell⟩ := by rw [hidxW]
        _ = idx.row := by simpa [idx] using hgetWCell
    have hfirstZ :
        V13RealLinearAdaptiveQRowTraceFirstCosetHit
          (v13RealLinearNoTargetRowsSequentialQRowExperiment i₀ observer)
          i₀
          (v13RealLinearNoTargetRowsSequentialQRowTrace i₀ observer)
          t (idx.A, cell.val) := by
      constructor
      · simpa [traceZ] using hlenZ
      · refine ⟨hlenZ, ?_⟩
        have hhit :
            V13RealLinearRowFunctionalTargetCosetHit idx.A.val idx.rows i₀
              (traceZ.get ⟨(t : Nat), hlenZ⟩) := by
          rw [hgetZ]
          exact idx.hit
        simpa [traceZ, htraceRowsZ,
          v13RealLinearNoTargetRowsSequentialQRowExperiment,
          v13RealLinearNoTargetRowsCausalQRowExperiment,
          v13RealLinearNoTargetRowsQRowExperiment] using hhit
    have hrowWitness :
        ∃ h : (t : Nat) < traceZ.length,
          traceZ.get ⟨(t : Nat), h⟩ = idx.row :=
      ⟨hlenZ, hgetZ⟩
    have htranscriptIdx :
        v13RealLinearRowsTranscript idx.rows publicZ = idx.transcript := by
      funext row
      have hrowG : row.1 ∈ G := by
        dsimp [G]
        simp [
          v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedQBudgetedRowset,
          idx, row.property]
      have hviewG := congrFun cell.property.2 ⟨row.1, hrowG⟩
      have hviewW := congrFun witness.property.2.2.2 row
      calc
        v13RealLinearRowsTranscript idx.rows publicZ row =
            v13RealLinearRowView row.1 publicZ := rfl
        _ = v13RealLinearRowView row.1 publicW := by
          simpa [G,
            v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedTranscript,
            witness, publicW,
            v13RealLinearRowsTranscript] using hviewG
        _ = idx.transcript row := by
          simpa [idx, v13RealLinearRowsTranscript] using hviewW
    exact
      ⟨cell.val, by
        exact ⟨hfirstZ, htraceRowsZ, hrowWitness, htranscriptIdx⟩⟩
  inj' := by
    intro cell₀ cell₁ hcell
    apply Subtype.ext
    exact
      congrArg
        (fun cell :
          V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinder
            i₀ observer t activeIdx.1 => cell.val)
        hcell

noncomputable def
    v13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinderSigmaEquivWorldSet
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q) :
    (Σ idx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinderIndex
        m q i₀ observer t,
      V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinder
        i₀ observer t idx) ≃
      V13RealLinearNoTargetSequentialTraceFirstCosetHitWorldSet
        i₀ observer t :=
  (v13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixTranscriptSigmaEquivFixedMapCylinderSigma
      i₀ observer t).symm.trans
    (v13RealLinearNoTargetSequentialTraceFirstCosetHitWorldSetEquivSigmaFixedPrefixTranscript
      i₀ observer t).symm

abbrev
    V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveGeneratedPrefixCellIncidence
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q) :=
  Σ activeIdx :
    V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
      i₀ observer t,
    V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderGeneratedPrefixCell
      i₀ observer t activeIdx

noncomputable instance
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q) :
    Fintype
      (V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveGeneratedPrefixCellIncidence
        i₀ observer t) := by
  classical
  unfold
    V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveGeneratedPrefixCellIncidence
  infer_instance

noncomputable def
    v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveGeneratedPrefixCellIncidenceToWorldSet
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q) :
    V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveGeneratedPrefixCellIncidence
        i₀ observer t ↪
      V13RealLinearNoTargetSequentialTraceFirstCosetHitWorldSet
        i₀ observer t where
  toFun incidence :=
    (v13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinderSigmaEquivWorldSet
        i₀ observer t)
      ⟨incidence.1.1,
        v13RealLinearNoTargetSequentialTraceFirstCosetHitGeneratedPrefixCellToFixedMapTranscriptCylinder
          i₀ observer t incidence.1 incidence.2⟩
  inj' := by
    classical
    rintro ⟨activeIdx₀, cell₀⟩ ⟨activeIdx₁, cell₁⟩ hworld
    let E :=
      v13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinderSigmaEquivWorldSet
        i₀ observer t
    have hsigma :
        (⟨activeIdx₀.1,
          v13RealLinearNoTargetSequentialTraceFirstCosetHitGeneratedPrefixCellToFixedMapTranscriptCylinder
            i₀ observer t activeIdx₀ cell₀⟩ :
          Σ idx :
            V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinderIndex
              m q i₀ observer t,
            V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedMapTranscriptCylinder
              i₀ observer t idx) =
        ⟨activeIdx₁.1,
          v13RealLinearNoTargetSequentialTraceFirstCosetHitGeneratedPrefixCellToFixedMapTranscriptCylinder
            i₀ observer t activeIdx₁ cell₁⟩ := by
      exact E.injective hworld
    have hactive : activeIdx₀ = activeIdx₁ := by
      apply Subtype.ext
      exact congrArg Sigma.fst hsigma
    cases hactive
    have hfixed :
        v13RealLinearNoTargetSequentialTraceFirstCosetHitGeneratedPrefixCellToFixedMapTranscriptCylinder
            i₀ observer t activeIdx₀ cell₀ =
          v13RealLinearNoTargetSequentialTraceFirstCosetHitGeneratedPrefixCellToFixedMapTranscriptCylinder
            i₀ observer t activeIdx₀ cell₁ := by
      simpa using hsigma
    have hcell : cell₀ = cell₁ := by
      exact
        (v13RealLinearNoTargetSequentialTraceFirstCosetHitGeneratedPrefixCellToFixedMapTranscriptCylinder
          i₀ observer t activeIdx₀).injective hfixed
    cases hcell
    rfl

theorem
    v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveGeneratedPrefixCellIncidence_card_le_worldSet
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q) :
    Fintype.card
        (V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveGeneratedPrefixCellIncidence
          i₀ observer t) ≤
      Fintype.card
        (V13RealLinearNoTargetSequentialTraceFirstCosetHitWorldSet
          i₀ observer t) :=
  Fintype.card_le_of_embedding
    (v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveGeneratedPrefixCellIncidenceToWorldSet
      i₀ observer t)

theorem
    v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveGeneratedPrefixCell_capacity_sum_le_worldSet_card
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q) :
    (∑ activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t,
      2 ^ (m -
        (v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedQBudgetedRowset
          i₀ observer t activeIdx).1.card)) ≤
      Fintype.card
        (V13RealLinearNoTargetSequentialTraceFirstCosetHitWorldSet
          i₀ observer t) := by
  classical
  calc
    (∑ activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t,
      2 ^ (m -
        (v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_generatedQBudgetedRowset
          i₀ observer t activeIdx).1.card)) =
        ∑ activeIdx :
          V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
            i₀ observer t,
          Fintype.card
            (V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderGeneratedPrefixCell
              i₀ observer t activeIdx) := by
          apply Finset.sum_congr rfl
          intro activeIdx _hactiveIdx
          rw [
            v13RealLinearNoTargetSequentialTraceFirstCosetHitGeneratedPrefixCell_card_eq_capacity
              i₀ observer t activeIdx]
    _ =
        Fintype.card
          (V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveGeneratedPrefixCellIncidence
            i₀ observer t) := by
          unfold
            V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveGeneratedPrefixCellIncidence
          exact
            (Fintype.card_sigma
              (α := fun activeIdx :
                V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
                  i₀ observer t =>
                V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderGeneratedPrefixCell
                  i₀ observer t activeIdx)).symm
    _ ≤
        Fintype.card
          (V13RealLinearNoTargetSequentialTraceFirstCosetHitWorldSet
            i₀ observer t) :=
          v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveGeneratedPrefixCellIncidence_card_le_worldSet
            i₀ observer t

/-- The full no-target first-hit event at step `t`, partitioned by the ordered
prefix transcript actually seen by the sequential observer before that step. -/
abbrev
    V13RealLinearNoTargetSequentialTraceFirstCosetHitOrderedPrefixWorldSet
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (pref :
      V13RealLinearSequentialPrefixTranscriptVector m (t : Nat)) :=
  {omega :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitWorldSet
        i₀ observer t //
    v13RealLinearSequentialPrefixTranscriptVectorOf observer
        (v13RealLinearPublicInput
          ({ x := omega.val.2, A := omega.val.1.val } :
            V13RealLinearWorld m))
        (t : Nat) =
      pref}

noncomputable instance
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (pref :
      V13RealLinearSequentialPrefixTranscriptVector m (t : Nat)) :
    Fintype
      (V13RealLinearNoTargetSequentialTraceFirstCosetHitOrderedPrefixWorldSet
        i₀ observer t pref) := by
  classical
  unfold
    V13RealLinearNoTargetSequentialTraceFirstCosetHitOrderedPrefixWorldSet
  infer_instance

/-- Full no-target worlds whose realized ordered prefix is exactly `pref`.
These classes partition the ambient no-target world space at a fixed step. -/
abbrev
    V13RealLinearNoTargetSequentialPrefixWorldSet
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (pref :
      V13RealLinearSequentialPrefixTranscriptVector m (t : Nat)) :=
  {omega :
      V13RealLinearAdaptiveQRowWorld m
        (V13RealLinearNoTargetRowsMap m i₀) //
    v13RealLinearSequentialPrefixTranscriptVectorOf observer
        (v13RealLinearPublicInput
          ({ x := omega.2, A := omega.1.val } : V13RealLinearWorld m))
        (t : Nat) =
      pref}

noncomputable instance
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (pref :
      V13RealLinearSequentialPrefixTranscriptVector m (t : Nat)) :
    Fintype
      (V13RealLinearNoTargetSequentialPrefixWorldSet
        i₀ observer t pref) := by
  classical
  unfold V13RealLinearNoTargetSequentialPrefixWorldSet
  infer_instance

/-- A canonical row view extracted from an ordered prefix for a row that occurs
in that prefix.  Repeated reads are coherent on realized prefixes; this choice
only fixes a representative occurrence for the conditioned map class below. -/
noncomputable def v13RealLinearSequentialPrefixTranscriptVectorRowView
    {m n : Nat} (pref : V13RealLinearSequentialPrefixTranscriptVector m n)
    (row :
      {row : Fin m //
        row ∈ v13RealLinearSequentialPrefixTranscriptVectorRows pref}) :
    V13RealLinearRowView m := by
  classical
  let transcript := v13RealLinearSequentialPrefixTranscriptVectorToList pref
  have hrowFinset : row.1 ∈ (transcript.map Prod.fst).toFinset := by
    exact row.2
  have hrowMap : row.1 ∈ transcript.map Prod.fst :=
    List.mem_toFinset.mp hrowFinset
  let entry := Classical.choose (List.mem_map.mp hrowMap)
  exact entry.2

theorem v13RealLinearSequentialPrefixTranscriptVectorRowView_spec
    {m n : Nat} (pref : V13RealLinearSequentialPrefixTranscriptVector m n)
    (row :
      {row : Fin m //
        row ∈ v13RealLinearSequentialPrefixTranscriptVectorRows pref}) :
    ∃ entry : Fin m × V13RealLinearRowView m,
      entry ∈ v13RealLinearSequentialPrefixTranscriptVectorToList pref ∧
        entry.1 = row.1 ∧
        v13RealLinearSequentialPrefixTranscriptVectorRowView pref row =
          entry.2 := by
  classical
  let transcript := v13RealLinearSequentialPrefixTranscriptVectorToList pref
  have hrowFinset : row.1 ∈ (transcript.map Prod.fst).toFinset := by
    exact row.2
  have hrowMap : row.1 ∈ transcript.map Prod.fst :=
    List.mem_toFinset.mp hrowFinset
  let entry := Classical.choose (List.mem_map.mp hrowMap)
  have hentry := Classical.choose_spec (List.mem_map.mp hrowMap)
  exact ⟨entry, hentry.1, hentry.2, rfl⟩

/-- Projection of a fixed ordered-prefix world class to its no-target maps. -/
abbrev V13RealLinearNoTargetSequentialPrefixMapClass
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (pref :
      V13RealLinearSequentialPrefixTranscriptVector m (t : Nat)) :=
  {A : V13RealLinearNoTargetRowsMap m i₀ //
    ∃ x : F2Vec m,
      v13RealLinearSequentialPrefixTranscriptVectorOf observer
          (v13RealLinearPublicInput
            ({ x := x, A := A.val } : V13RealLinearWorld m))
          (t : Nat) =
        pref}

noncomputable instance
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (pref :
      V13RealLinearSequentialPrefixTranscriptVector m (t : Nat)) :
    Fintype
      (V13RealLinearNoTargetSequentialPrefixMapClass
        i₀ observer t pref) := by
  classical
  unfold V13RealLinearNoTargetSequentialPrefixMapClass
  infer_instance

noncomputable def v13RealLinearNoTargetSequentialPrefixMapClassWitness
    {m q : Nat} {i₀ : Fin m}
    {observer : V13RealLinearSequentialRowObserver m q} {t : Fin q}
    {pref :
      V13RealLinearSequentialPrefixTranscriptVector m (t : Nat)}
    (A :
      V13RealLinearNoTargetSequentialPrefixMapClass
        i₀ observer t pref) : F2Vec m :=
  Classical.choose A.property

theorem v13RealLinearNoTargetSequentialPrefixMapClassWitness_property
    {m q : Nat} {i₀ : Fin m}
    {observer : V13RealLinearSequentialRowObserver m q} {t : Fin q}
    {pref :
      V13RealLinearSequentialPrefixTranscriptVector m (t : Nat)}
    (A :
      V13RealLinearNoTargetSequentialPrefixMapClass
        i₀ observer t pref) :
    v13RealLinearSequentialPrefixTranscriptVectorOf observer
        (v13RealLinearPublicInput
          ({ x := v13RealLinearNoTargetSequentialPrefixMapClassWitness A,
             A := A.val.val } : V13RealLinearWorld m))
        (t : Nat) =
      pref :=
  Classical.choose_spec A.property

theorem
    v13RealLinearNoTargetSequentialPrefixMapClass_rowView_eq
    {m q : Nat} {i₀ : Fin m}
    {observer : V13RealLinearSequentialRowObserver m q} {t : Fin q}
    {pref :
      V13RealLinearSequentialPrefixTranscriptVector m (t : Nat)}
    (A :
      V13RealLinearNoTargetSequentialPrefixMapClass
        i₀ observer t pref)
    (row :
      {row : Fin m //
        row ∈ v13RealLinearSequentialPrefixTranscriptVectorRows pref}) :
    v13RealLinearSequentialPrefixTranscriptVectorRowView pref row =
      v13RealLinearRowView row.1
        (v13RealLinearPublicInput
          ({ x := v13RealLinearNoTargetSequentialPrefixMapClassWitness A,
             A := A.val.val } : V13RealLinearWorld m)) := by
  classical
  rcases
      v13RealLinearSequentialPrefixTranscriptVectorRowView_spec pref row with
    ⟨entry, hentry, hentryRow, hrowView⟩
  have hpref :=
    v13RealLinearNoTargetSequentialPrefixMapClassWitness_property A
  have hlist :
      v13RealLinearSequentialPrefixTranscriptVectorToList pref =
        v13RealLinearSequentialRowPrefixTranscriptOf observer
          (v13RealLinearPublicInput
            ({ x := v13RealLinearNoTargetSequentialPrefixMapClassWitness A,
               A := A.val.val } : V13RealLinearWorld m))
          (t : Nat) := by
    have h :=
      congrArg v13RealLinearSequentialPrefixTranscriptVectorToList
        hpref.symm
    simpa [v13RealLinearSequentialPrefixTranscriptVectorOf_toList]
      using h
  have hentryActual :
      entry ∈
        v13RealLinearSequentialRowPrefixTranscriptOf observer
          (v13RealLinearPublicInput
            ({ x := v13RealLinearNoTargetSequentialPrefixMapClassWitness A,
               A := A.val.val } : V13RealLinearWorld m))
          (t : Nat) := by
    simpa [hlist] using hentry
  have hviewActual :=
    v13RealLinearSequentialRowPrefixTranscriptOf_mem_view
      observer
      (v13RealLinearPublicInput
        ({ x := v13RealLinearNoTargetSequentialPrefixMapClassWitness A,
           A := A.val.val } : V13RealLinearWorld m))
      (t : Nat) hentryActual
  calc
    v13RealLinearSequentialPrefixTranscriptVectorRowView pref row =
        entry.2 := hrowView
    _ =
        v13RealLinearRowView entry.1
          (v13RealLinearPublicInput
            ({ x := v13RealLinearNoTargetSequentialPrefixMapClassWitness A,
               A := A.val.val } : V13RealLinearWorld m)) := hviewActual
    _ =
        v13RealLinearRowView row.1
          (v13RealLinearPublicInput
            ({ x := v13RealLinearNoTargetSequentialPrefixMapClassWitness A,
               A := A.val.val } : V13RealLinearWorld m)) := by
          rw [hentryRow]

theorem
    v13RealLinearNoTargetSequentialPrefixMapClass_rowFunctional_eq
    {m q : Nat} {i₀ : Fin m}
    {observer : V13RealLinearSequentialRowObserver m q} {t : Fin q}
    {pref :
      V13RealLinearSequentialPrefixTranscriptVector m (t : Nat)}
    (A :
      V13RealLinearNoTargetSequentialPrefixMapClass
        i₀ observer t pref)
    (row :
      {row : Fin m //
        row ∈ v13RealLinearSequentialPrefixTranscriptVectorRows pref})
    (w : F2Vec m) :
    A.val.val.toEquiv w row.1 =
      (v13RealLinearSequentialPrefixTranscriptVectorRowView pref row).1 w := by
  have hview :=
    v13RealLinearNoTargetSequentialPrefixMapClass_rowView_eq A row
  have hfirst := congrArg Prod.fst hview
  simpa [v13RealLinearRowView, v13RealLinearPublicInput] using
    (congrFun hfirst w).symm

theorem
    v13RealLinearSequentialPrefixTranscriptVectorOf_eq_of_rowView_eq_on_rows
    {m q n : Nat} (observer : V13RealLinearSequentialRowObserver m q)
    {public₀ public₁ : V13RealLinearPublic m}
    {pref : V13RealLinearSequentialPrefixTranscriptVector m n}
    (hpref₀ :
      v13RealLinearSequentialPrefixTranscriptVectorOf observer public₀ n =
        pref)
    (hsame :
      ∀ row : Fin m,
        row ∈ v13RealLinearSequentialPrefixTranscriptVectorRows pref →
          v13RealLinearRowView row public₁ =
            v13RealLinearRowView row public₀) :
    v13RealLinearSequentialPrefixTranscriptVectorOf observer public₁ n =
      pref := by
  classical
  have hrows₀ :
      v13RealLinearSequentialRowTranscriptRows
          (v13RealLinearSequentialRowPrefixTranscriptOf observer public₀ n) =
        v13RealLinearSequentialPrefixTranscriptVectorRows pref := by
    have hrows :=
      congrArg v13RealLinearSequentialPrefixTranscriptVectorRows hpref₀
    simpa [v13RealLinearSequentialPrefixTranscriptVectorOf_rows]
      using hrows
  have hsameRows :
      v13RealLinearRowsTranscript
          (v13RealLinearSequentialRowTranscriptRows
            (v13RealLinearSequentialRowPrefixTranscriptOf observer public₀ n))
          public₀ =
        v13RealLinearRowsTranscript
          (v13RealLinearSequentialRowTranscriptRows
            (v13RealLinearSequentialRowPrefixTranscriptOf observer public₀ n))
          public₁ := by
    funext row
    have hrowPref :
        row.1 ∈ v13RealLinearSequentialPrefixTranscriptVectorRows pref := by
      rw [← hrows₀]
      exact row.2
    exact (hsame row.1 hrowPref).symm
  have hprefix :
      v13RealLinearSequentialRowPrefixTranscriptOf observer public₁ n =
        v13RealLinearSequentialRowPrefixTranscriptOf observer public₀ n := by
    simpa [v13RealLinearSequentialRowPrefixTranscriptOf] using
      v13RealLinearSequentialRowRunAux_eq_of_final_rowsTranscript_eq
        observer public₀ public₁ n [] hsameRows
  have hlist :
      v13RealLinearSequentialPrefixTranscriptVectorToList
          (v13RealLinearSequentialPrefixTranscriptVectorOf observer
            public₁ n) =
        v13RealLinearSequentialPrefixTranscriptVectorToList pref := by
    calc
      v13RealLinearSequentialPrefixTranscriptVectorToList
          (v13RealLinearSequentialPrefixTranscriptVectorOf observer
            public₁ n) =
        v13RealLinearSequentialRowPrefixTranscriptOf observer public₁ n := by
          rw [v13RealLinearSequentialPrefixTranscriptVectorOf_toList]
      _ =
        v13RealLinearSequentialRowPrefixTranscriptOf observer public₀ n :=
          hprefix
      _ =
        v13RealLinearSequentialPrefixTranscriptVectorToList
          (v13RealLinearSequentialPrefixTranscriptVectorOf observer
            public₀ n) := by
          rw [v13RealLinearSequentialPrefixTranscriptVectorOf_toList]
      _ =
        v13RealLinearSequentialPrefixTranscriptVectorToList pref := by
          rw [hpref₀]
  exact List.ofFn_inj.mp hlist

/-- Maps in a fixed prefix class whose fresh row is pinned to the target plus
the recorded functionals on a fixed nonempty prefix support. -/
abbrev V13RealLinearNoTargetSequentialPrefixPinnedSupportMapClass
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (pref :
      V13RealLinearSequentialPrefixTranscriptVector m (t : Nat))
    (row₁ : Fin m)
    (support :
      Finset
        {row : Fin m //
          row ∈ v13RealLinearSequentialPrefixTranscriptVectorRows pref}) :=
  {A :
      V13RealLinearNoTargetSequentialPrefixMapClass
        i₀ observer t pref //
    ∀ w : F2Vec m,
      A.val.val.toEquiv w row₁ =
        w i₀ +
          support.sum
            (fun row =>
              (v13RealLinearSequentialPrefixTranscriptVectorRowView
                pref row).1 w)}

noncomputable instance
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (pref :
      V13RealLinearSequentialPrefixTranscriptVector m (t : Nat))
    (row₁ : Fin m)
    (support :
      Finset
        {row : Fin m //
          row ∈ v13RealLinearSequentialPrefixTranscriptVectorRows pref}) :
    Fintype
      (V13RealLinearNoTargetSequentialPrefixPinnedSupportMapClass
        i₀ observer t pref row₁ support) := by
  classical
  unfold V13RealLinearNoTargetSequentialPrefixPinnedSupportMapClass
  infer_instance

noncomputable def
    v13RealLinearNoTargetSequentialPrefixPinnedSupportMapClassToFixedSupport
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (pref :
      V13RealLinearSequentialPrefixTranscriptVector m (t : Nat))
    {row₁ : Fin m}
    (hrow₁ :
      row₁ ∉ v13RealLinearSequentialPrefixTranscriptVectorRows pref)
    (support :
      Finset
        {row : Fin m //
          row ∈ v13RealLinearSequentialPrefixTranscriptVectorRows pref})
    (A :
      V13RealLinearNoTargetSequentialPrefixPinnedSupportMapClass
        i₀ observer t pref row₁ support) :
    V13RealLinearNoTargetFixedSupportSumTargetMapSet i₀
      (v13RealLinearFreshFullSupport
        (v13RealLinearSequentialPrefixTranscriptVectorRows pref)
        row₁ support) := by
  classical
  refine ⟨A.val.val, ?_⟩
  intro w
  have hsupport :
      support.sum (fun row => A.val.val.val.toEquiv w row.1) =
        support.sum
          (fun row =>
            (v13RealLinearSequentialPrefixTranscriptVectorRowView
              pref row).1 w) := by
    apply Finset.sum_congr rfl
    intro row _hrow
    exact
      v13RealLinearNoTargetSequentialPrefixMapClass_rowFunctional_eq
        A.val row w
  calc
    (v13RealLinearFreshFullSupport
        (v13RealLinearSequentialPrefixTranscriptVectorRows pref)
        row₁ support).sum
        (fun row => A.val.val.val.toEquiv w row.1) =
      A.val.val.val.toEquiv w row₁ +
        support.sum (fun row => A.val.val.val.toEquiv w row.1) :=
        v13RealLinearFreshFullSupport_sum
          A.val.val.val hrow₁ support w
    _ =
      (w i₀ +
          support.sum
            (fun row =>
              (v13RealLinearSequentialPrefixTranscriptVectorRowView
                pref row).1 w)) +
        support.sum (fun row => A.val.val.val.toEquiv w row.1) := by
          rw [A.property w]
    _ =
      (w i₀ +
          support.sum
            (fun row =>
              (v13RealLinearSequentialPrefixTranscriptVectorRowView
                pref row).1 w)) +
        support.sum
          (fun row =>
            (v13RealLinearSequentialPrefixTranscriptVectorRowView
              pref row).1 w) := by
          rw [hsupport]
    _ = w i₀ := by
      exact
        f2_add_right_self (w i₀)
          (support.sum
            (fun row =>
              (v13RealLinearSequentialPrefixTranscriptVectorRowView
                pref row).1 w))

noncomputable def
    v13RealLinearNoTargetSequentialPrefixPinnedSupportShearMap
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (pref :
      V13RealLinearSequentialPrefixTranscriptVector m (t : Nat))
    {row₁ : Fin m}
    (hrow₁ :
      row₁ ∉ v13RealLinearSequentialPrefixTranscriptVectorRows pref)
    {support :
      Finset
        {row : Fin m //
          row ∈ v13RealLinearSequentialPrefixTranscriptVectorRows pref}}
    (row₀ :
      {row : Fin m //
        row ∈ v13RealLinearSequentialPrefixTranscriptVectorRows pref})
    (hrow₀ : row₀ ∈ support)
    (A :
      V13RealLinearNoTargetSequentialPrefixPinnedSupportMapClass
        i₀ observer t pref row₁ support)
    (s : V13RealLinearTwoRowZeroAt row₀.1 row₁) :
    V13RealLinearNoTargetRowsMap m i₀ := by
  classical
  let rows := v13RealLinearSequentialPrefixTranscriptVectorRows pref
  let row₀Full : {row : Fin m // row ∈ insert row₁ rows} :=
    ⟨row₀.1, Finset.mem_insert_of_mem (by simp [rows, row₀.2])⟩
  let row₁Full : {row : Fin m // row ∈ insert row₁ rows} :=
    ⟨row₁, Finset.mem_insert_self row₁ rows⟩
  have hrow₀Full :
      row₀Full ∈ v13RealLinearFreshFullSupport rows row₁ support := by
    simp [row₀Full, rows, v13RealLinearFreshFullSupport,
      v13RealLinearInsertRowsEmbedding, hrow₀]
  have hrow₁Full :
      row₁Full ∈ v13RealLinearFreshFullSupport rows row₁ support := by
    simp [row₁Full, v13RealLinearFreshFullSupport]
  have hneqFull : row₀Full ≠ row₁Full := by
    intro hbad
    have hval := congrArg
      (fun row : {row : Fin m // row ∈ insert row₁ rows} => row.1)
      hbad
    have hval' : row₀.1 = row₁ := by
      simpa [row₀Full, row₁Full] using hval
    exact hrow₁ (by rw [← hval']; exact row₀.2)
  exact
    ⟨v13RealLinearComp
        (v13RealLinearTwoRowZeroShear row₀.1 row₁ s) A.val.val.val,
      v13RealLinearNoTargetFixedSupportSumTarget_shear_targetRows_empty
        i₀ row₀Full row₁Full hrow₀Full hrow₁Full hneqFull
        (v13RealLinearNoTargetSequentialPrefixPinnedSupportMapClassToFixedSupport
          i₀ observer t pref hrow₁ support A)
        s⟩

theorem
    v13RealLinearNoTargetSequentialPrefixPinnedSupportShearMap_prefix
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (pref :
      V13RealLinearSequentialPrefixTranscriptVector m (t : Nat))
    {row₁ : Fin m}
    (hrow₁ :
      row₁ ∉ v13RealLinearSequentialPrefixTranscriptVectorRows pref)
    {support :
      Finset
        {row : Fin m //
          row ∈ v13RealLinearSequentialPrefixTranscriptVectorRows pref}}
    (row₀ :
      {row : Fin m //
        row ∈ v13RealLinearSequentialPrefixTranscriptVectorRows pref})
    (hrow₀ : row₀ ∈ support)
    (A :
      V13RealLinearNoTargetSequentialPrefixPinnedSupportMapClass
        i₀ observer t pref row₁ support)
    (s : V13RealLinearTwoRowZeroAt row₀.1 row₁) :
    v13RealLinearSequentialPrefixTranscriptVectorOf observer
        (v13RealLinearPublicInput
          ({ x := v13RealLinearNoTargetSequentialPrefixMapClassWitness A.val,
             A :=
              (v13RealLinearNoTargetSequentialPrefixPinnedSupportShearMap
                i₀ observer t pref hrow₁ row₀ hrow₀ A s).val } :
            V13RealLinearWorld m))
        (t : Nat) =
      pref := by
  classical
  let x := v13RealLinearNoTargetSequentialPrefixMapClassWitness A.val
  let B :=
    v13RealLinearNoTargetSequentialPrefixPinnedSupportShearMap
      i₀ observer t pref hrow₁ row₀ hrow₀ A s
  have hprefA :=
    v13RealLinearNoTargetSequentialPrefixMapClassWitness_property A.val
  apply
    v13RealLinearSequentialPrefixTranscriptVectorOf_eq_of_rowView_eq_on_rows
      observer hprefA
  intro row hrow
  have hne : row ≠ row₁ := by
    intro h
    exact hrow₁ (by simpa [h] using hrow)
  apply Prod.ext
  · funext probe
    simpa [
      v13RealLinearNoTargetSequentialPrefixPinnedSupportShearMap,
      v13RealLinearNoTargetFixedSupportSumTargetShear,
      v13RealLinearNoTargetSequentialPrefixPinnedSupportMapClassToFixedSupport,
      v13RealLinearComp, v13RealLinearRowView, v13RealLinearPublicInput] using
      v13RealLinearTwoRowZeroShear_apply_of_ne
        row₀.1 row₁ s (A.val.val.val.toEquiv probe) hne
  · simpa [
      v13RealLinearNoTargetSequentialPrefixPinnedSupportShearMap,
      v13RealLinearNoTargetFixedSupportSumTargetShear,
      v13RealLinearNoTargetSequentialPrefixPinnedSupportMapClassToFixedSupport,
      v13RealLinearComp, v13RealLinearRowView, v13RealLinearPublicInput] using
      v13RealLinearTwoRowZeroShear_apply_of_ne
        row₀.1 row₁ s (A.val.val.val.toEquiv x) hne

noncomputable def
    v13RealLinearNoTargetSequentialPrefixPinnedSupportShear
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (pref :
      V13RealLinearSequentialPrefixTranscriptVector m (t : Nat))
    {row₁ : Fin m}
    (hrow₁ :
      row₁ ∉ v13RealLinearSequentialPrefixTranscriptVectorRows pref)
    {support :
      Finset
        {row : Fin m //
          row ∈ v13RealLinearSequentialPrefixTranscriptVectorRows pref}}
    (row₀ :
      {row : Fin m //
        row ∈ v13RealLinearSequentialPrefixTranscriptVectorRows pref})
    (hrow₀ : row₀ ∈ support)
    (A :
      V13RealLinearNoTargetSequentialPrefixPinnedSupportMapClass
        i₀ observer t pref row₁ support)
    (s : V13RealLinearTwoRowZeroAt row₀.1 row₁) :
    V13RealLinearNoTargetSequentialPrefixMapClass
      i₀ observer t pref :=
  ⟨v13RealLinearNoTargetSequentialPrefixPinnedSupportShearMap
      i₀ observer t pref hrow₁ row₀ hrow₀ A s,
    ⟨v13RealLinearNoTargetSequentialPrefixMapClassWitness A.val,
      v13RealLinearNoTargetSequentialPrefixPinnedSupportShearMap_prefix
        i₀ observer t pref hrow₁ row₀ hrow₀ A s⟩⟩

noncomputable def
    v13RealLinearNoTargetSequentialPrefixPinnedSupportShearFunction
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (pref :
      V13RealLinearSequentialPrefixTranscriptVector m (t : Nat))
    {row₁ : Fin m}
    (hrow₁ :
      row₁ ∉ v13RealLinearSequentialPrefixTranscriptVectorRows pref)
    {support :
      Finset
        {row : Fin m //
          row ∈ v13RealLinearSequentialPrefixTranscriptVectorRows pref}}
    (row₀ :
      {row : Fin m //
        row ∈ v13RealLinearSequentialPrefixTranscriptVectorRows pref})
    (hrow₀ : row₀ ∈ support)
    (pair :
    V13RealLinearNoTargetSequentialPrefixPinnedSupportMapClass
        i₀ observer t pref row₁ support ×
      V13RealLinearTwoRowZeroAt row₀.1 row₁) :
    V13RealLinearNoTargetSequentialPrefixMapClass
        i₀ observer t pref :=
  ⟨v13RealLinearNoTargetSequentialPrefixPinnedSupportShearMap
      i₀ observer t pref hrow₁ row₀ hrow₀ pair.1 pair.2,
    ⟨v13RealLinearNoTargetSequentialPrefixMapClassWitness pair.1.val,
      v13RealLinearNoTargetSequentialPrefixPinnedSupportShearMap_prefix
        i₀ observer t pref hrow₁ row₀ hrow₀ pair.1 pair.2⟩⟩

theorem
    v13RealLinearNoTargetSequentialPrefixPinnedSupportShearMap_inj
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (pref :
      V13RealLinearSequentialPrefixTranscriptVector m (t : Nat))
    {row₁ : Fin m}
    (hrow₁ :
      row₁ ∉ v13RealLinearSequentialPrefixTranscriptVectorRows pref)
    {support :
      Finset
        {row : Fin m //
          row ∈ v13RealLinearSequentialPrefixTranscriptVectorRows pref}}
    (row₀ :
      {row : Fin m //
        row ∈ v13RealLinearSequentialPrefixTranscriptVectorRows pref})
    (hrow₀ : row₀ ∈ support)
    {A₀ A₁ :
      V13RealLinearNoTargetSequentialPrefixPinnedSupportMapClass
        i₀ observer t pref row₁ support}
    {s₀ s₁ : V13RealLinearTwoRowZeroAt row₀.1 row₁}
    (hmap :
      v13RealLinearNoTargetSequentialPrefixPinnedSupportShearMap
          i₀ observer t pref hrow₁ row₀ hrow₀ A₀ s₀ =
        v13RealLinearNoTargetSequentialPrefixPinnedSupportShearMap
          i₀ observer t pref hrow₁ row₀ hrow₀ A₁ s₁) :
    (A₀, s₀) = (A₁, s₁) := by
  classical
  have hB :
      v13RealLinearComp
          (v13RealLinearTwoRowZeroShear row₀.1 row₁ s₀)
          A₀.val.val.val =
        v13RealLinearComp
          (v13RealLinearTwoRowZeroShear row₀.1 row₁ s₁)
          A₁.val.val.val := by
    simpa [v13RealLinearNoTargetSequentialPrefixPinnedSupportShearMap]
      using congrArg Subtype.val hmap
  have hrowEqOfNe :
      ∀ (row : Fin m), row ≠ row₁ →
        ∀ w : F2Vec m,
          A₀.val.val.val.toEquiv w row =
            A₁.val.val.val.toEquiv w row := by
    intro row hrow w
    have h := congrFun (congrArg
      (fun A : V13F2LinearEquiv m => A.toEquiv w) hB) row
    simpa [v13RealLinearComp,
      v13RealLinearTwoRowZeroShear_apply_of_ne row₀.1 row₁ s₀
        (A₀.val.val.val.toEquiv w) hrow,
      v13RealLinearTwoRowZeroShear_apply_of_ne row₀.1 row₁ s₁
        (A₁.val.val.val.toEquiv w) hrow] using h
  have hrow₁Eq :
      ∀ w : F2Vec m,
        A₀.val.val.val.toEquiv w row₁ =
          A₁.val.val.val.toEquiv w row₁ := by
    intro w
    rw [A₀.property w, A₁.property w]
  have hAmap : A₀.val.val = A₁.val.val := by
    apply Subtype.ext
    apply v13RealLinearEquiv_ext
    intro w
    funext row
    by_cases hrow : row = row₁
    · subst row
      exact hrow₁Eq w
    · exact hrowEqOfNe row hrow w
  have hA : A₀ = A₁ := by
    apply Subtype.ext
    apply Subtype.ext
    exact hAmap
  subst A₁
  have hs : s₀ = s₁ := by
    apply Subtype.ext
    funext row
    by_cases hrow₀Val : row = row₀.1
    · subst row
      rw [s₀.property.1, s₁.property.1]
    · by_cases hrow₁Val : row = row₁
      · subst row
        rw [s₀.property.2, s₁.property.2]
      · let probe : F2Vec m :=
          A₀.val.val.val.toEquiv.symm (v13RealLinearSingleBit row)
        have h := congrFun (congrArg
          (fun A : V13F2LinearEquiv m => A.toEquiv probe) hB) row₁
        have hsum₀ :
            v13RealLinearTwoRowZeroShearSum row₀.1 row₁ s₀
                (A₀.val.val.val.toEquiv probe) = s₀.val row := by
          simpa [probe] using
            (v13RealLinearTwoRowZeroShearSum_singleBit
              row₀.1 row₁ s₀ hrow₁Val)
        have hsum₁ :
            v13RealLinearTwoRowZeroShearSum row₀.1 row₁ s₁
                (A₀.val.val.val.toEquiv probe) = s₁.val row := by
          simpa [probe] using
            (v13RealLinearTwoRowZeroShearSum_singleBit
              row₀.1 row₁ s₁ hrow₁Val)
        simpa [v13RealLinearComp,
          v13RealLinearTwoRowZeroShear_apply_row₁,
          hsum₀, hsum₁] using h
  subst s₁
  rfl

noncomputable def
    v13RealLinearNoTargetSequentialPrefixPinnedSupportShearEmbedding
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (pref :
      V13RealLinearSequentialPrefixTranscriptVector m (t : Nat))
    {row₁ : Fin m}
    (hrow₁ :
      row₁ ∉ v13RealLinearSequentialPrefixTranscriptVectorRows pref)
    {support :
      Finset
        {row : Fin m //
          row ∈ v13RealLinearSequentialPrefixTranscriptVectorRows pref}}
    (row₀ :
      {row : Fin m //
        row ∈ v13RealLinearSequentialPrefixTranscriptVectorRows pref})
    (hrow₀ : row₀ ∈ support) :
    V13RealLinearNoTargetSequentialPrefixPinnedSupportMapClass
        i₀ observer t pref row₁ support ×
      V13RealLinearTwoRowZeroAt row₀.1 row₁ ↪
    V13RealLinearNoTargetSequentialPrefixMapClass
        i₀ observer t pref where
  toFun :=
    v13RealLinearNoTargetSequentialPrefixPinnedSupportShearFunction
      i₀ observer t pref hrow₁ row₀ hrow₀
  inj' := by
    intro pair₀ pair₁ hmap
    rcases pair₀ with ⟨A₀, s₀⟩
    rcases pair₁ with ⟨A₁, s₁⟩
    have hmapVal :
        v13RealLinearNoTargetSequentialPrefixPinnedSupportShearMap
            i₀ observer t pref hrow₁ row₀ hrow₀ A₀ s₀ =
          v13RealLinearNoTargetSequentialPrefixPinnedSupportShearMap
            i₀ observer t pref hrow₁ row₀ hrow₀ A₁ s₁ :=
      congrArg Subtype.val hmap
    exact
      v13RealLinearNoTargetSequentialPrefixPinnedSupportShearMap_inj
        i₀ observer t pref hrow₁ row₀ hrow₀ hmapVal

theorem
    v13RealLinearNoTargetSequentialPrefixPinnedSupportMapClass_card_mul_two_pow_le_prefixMapClass
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (pref :
      V13RealLinearSequentialPrefixTranscriptVector m (t : Nat))
    {row₁ : Fin m}
    (hrow₁ :
      row₁ ∉ v13RealLinearSequentialPrefixTranscriptVectorRows pref)
    {support :
      Finset
        {row : Fin m //
          row ∈ v13RealLinearSequentialPrefixTranscriptVectorRows pref}}
    (row₀ :
      {row : Fin m //
        row ∈ v13RealLinearSequentialPrefixTranscriptVectorRows pref})
    (hrow₀ : row₀ ∈ support) :
    Fintype.card
        (V13RealLinearNoTargetSequentialPrefixPinnedSupportMapClass
          i₀ observer t pref row₁ support) *
      2 ^ m ≤
    4 *
      Fintype.card
        (V13RealLinearNoTargetSequentialPrefixMapClass
          i₀ observer t pref) := by
  classical
  let S :=
    Fintype.card
      (V13RealLinearNoTargetSequentialPrefixPinnedSupportMapClass
        i₀ observer t pref row₁ support)
  let Z := Fintype.card (V13RealLinearTwoRowZeroAt row₀.1 row₁)
  let N :=
    Fintype.card
      (V13RealLinearNoTargetSequentialPrefixMapClass
        i₀ observer t pref)
  have hSZ : S * Z ≤ N := by
    simpa [S, Z, N, Fintype.card_prod] using
      Fintype.card_le_of_embedding
        (v13RealLinearNoTargetSequentialPrefixPinnedSupportShearEmbedding
          i₀ observer t pref hrow₁ row₀ hrow₀)
  have hneq : row₀.1 ≠ row₁ := by
    intro h
    exact hrow₁ (by simpa [h] using row₀.2)
  have hZ : Z * 4 = 2 ^ m := by
    simpa [Z] using
      v13RealLinearTwoRowZeroAt_card_mul_four row₀.1 row₁ hneq
  calc
    S * 2 ^ m = S * (Z * 4) := by rw [hZ]
    _ = 4 * (S * Z) := by ring
    _ ≤ 4 * N := Nat.mul_le_mul_left 4 hSZ

abbrev V13RealLinearNoTargetSequentialPrefixHitMapClass
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (pref :
      V13RealLinearSequentialPrefixTranscriptVector m (t : Nat))
    (row₁ : Fin m) :=
  {A :
      V13RealLinearNoTargetSequentialPrefixMapClass
        i₀ observer t pref //
    V13RealLinearRowFunctionalTargetCosetHit A.val.val
      (v13RealLinearSequentialPrefixTranscriptVectorRows pref) i₀ row₁}

noncomputable instance
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (pref :
      V13RealLinearSequentialPrefixTranscriptVector m (t : Nat))
    (row₁ : Fin m) :
    Fintype
      (V13RealLinearNoTargetSequentialPrefixHitMapClass
        i₀ observer t pref row₁) := by
  classical
  unfold V13RealLinearNoTargetSequentialPrefixHitMapClass
  infer_instance

abbrev V13RealLinearNoTargetSequentialPrefixHitSupportSigma
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (pref :
      V13RealLinearSequentialPrefixTranscriptVector m (t : Nat))
    (row₁ : Fin m) :=
  Σ support :
      {support :
        Finset
          {row : Fin m //
            row ∈ v13RealLinearSequentialPrefixTranscriptVectorRows pref} //
        0 < support.card},
    V13RealLinearNoTargetSequentialPrefixPinnedSupportMapClass
      i₀ observer t pref row₁ support.val

noncomputable instance
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (pref :
      V13RealLinearSequentialPrefixTranscriptVector m (t : Nat))
    (row₁ : Fin m) :
    Fintype
      (V13RealLinearNoTargetSequentialPrefixHitSupportSigma
        i₀ observer t pref row₁) := by
  classical
  unfold V13RealLinearNoTargetSequentialPrefixHitSupportSigma
  infer_instance

noncomputable def
    v13RealLinearNoTargetSequentialPrefixHitMapClassToSupportSigma
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (pref :
      V13RealLinearSequentialPrefixTranscriptVector m (t : Nat))
    {row₁ : Fin m}
    (hrow₁ :
      row₁ ∉ v13RealLinearSequentialPrefixTranscriptVectorRows pref) :
    V13RealLinearNoTargetSequentialPrefixHitMapClass
        i₀ observer t pref row₁ ↪
      V13RealLinearNoTargetSequentialPrefixHitSupportSigma
        i₀ observer t pref row₁ where
  toFun A := by
    classical
    let rows := v13RealLinearSequentialPrefixTranscriptVectorRows pref
    let ex :=
      v13RealLinearNoTargetRows_freshRowFunctionalTargetCosetHit_exists_support_sum
        A.val.val hrow₁ A.property
    let support := Classical.choose ex
    have hspec := Classical.choose_spec ex
    refine ⟨⟨support, hspec.1⟩, ⟨A.val, ?_⟩⟩
    intro w
    have hsupport :
        support.sum (fun row => A.val.val.val.toEquiv w row.1) =
          support.sum
            (fun row =>
              (v13RealLinearSequentialPrefixTranscriptVectorRowView
                pref row).1 w) := by
      apply Finset.sum_congr rfl
      intro row _hrow
      exact
        v13RealLinearNoTargetSequentialPrefixMapClass_rowFunctional_eq
          A.val row w
    have hfresh :=
      v13RealLinearFreshFullSupport_sum
        A.val.val.val hrow₁ support w
    have hfull := hspec.2 w
    have hrowPlus :
        A.val.val.val.toEquiv w row₁ +
          support.sum
            (fun row =>
              (v13RealLinearSequentialPrefixTranscriptVectorRowView
                pref row).1 w) =
        w i₀ := by
      rw [← hfull]
      rw [hfresh]
      rw [hsupport]
    calc
      A.val.val.val.toEquiv w row₁ =
          (A.val.val.val.toEquiv w row₁ +
            support.sum
              (fun row =>
                (v13RealLinearSequentialPrefixTranscriptVectorRowView
                  pref row).1 w)) +
            support.sum
              (fun row =>
                (v13RealLinearSequentialPrefixTranscriptVectorRowView
                  pref row).1 w) := by
            exact
              (f2_add_right_self
                (A.val.val.val.toEquiv w row₁)
                (support.sum
                  (fun row =>
                    (v13RealLinearSequentialPrefixTranscriptVectorRowView
                      pref row).1 w))).symm
      _ =
          w i₀ +
            support.sum
              (fun row =>
                (v13RealLinearSequentialPrefixTranscriptVectorRowView
                  pref row).1 w) := by
            rw [hrowPlus]
  inj' := by
    intro A₀ A₁ h
    apply Subtype.ext
    exact congrArg (fun z :
      V13RealLinearNoTargetSequentialPrefixHitSupportSigma
        i₀ observer t pref row₁ => z.2.val) h

theorem
    v13RealLinearNoTargetSequentialPrefixHitMapClass_card_mul_two_pow_le_prefixMapClass
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (pref :
      V13RealLinearSequentialPrefixTranscriptVector m (t : Nat))
    {row₁ : Fin m}
    (hrow₁ :
      row₁ ∉ v13RealLinearSequentialPrefixTranscriptVectorRows pref) :
    Fintype.card
        (V13RealLinearNoTargetSequentialPrefixHitMapClass
          i₀ observer t pref row₁) *
      2 ^ m ≤
    4 *
      2 ^ (v13RealLinearSequentialPrefixTranscriptVectorRows pref).card *
      Fintype.card
        (V13RealLinearNoTargetSequentialPrefixMapClass
          i₀ observer t pref) := by
  classical
  let rows := v13RealLinearSequentialPrefixTranscriptVectorRows pref
  let Hit :=
    V13RealLinearNoTargetSequentialPrefixHitMapClass
      i₀ observer t pref row₁
  let Sigma :=
    V13RealLinearNoTargetSequentialPrefixHitSupportSigma
      i₀ observer t pref row₁
  let N :=
    Fintype.card
      (V13RealLinearNoTargetSequentialPrefixMapClass
        i₀ observer t pref)
  let M := 2 ^ m
  have hHitLe :
      Fintype.card Hit ≤ Fintype.card Sigma :=
    Fintype.card_le_of_embedding
      (v13RealLinearNoTargetSequentialPrefixHitMapClassToSupportSigma
        i₀ observer t pref hrow₁)
  have hSupportLe :
      Fintype.card
          {support : Finset {row : Fin m // row ∈ rows} //
            0 < support.card} ≤
        2 ^ rows.card := by
    calc
      Fintype.card
          {support : Finset {row : Fin m // row ∈ rows} //
            0 < support.card} ≤
          Fintype.card (Finset {row : Fin m // row ∈ rows}) := by
        exact Fintype.card_subtype_le
          (fun support : Finset {row : Fin m // row ∈ rows} =>
            0 < support.card)
      _ = 2 ^ Fintype.card {row : Fin m // row ∈ rows} :=
        Fintype.card_finset
      _ = 2 ^ rows.card := by simp
  have hterm :
      ∀ support :
          {support : Finset {row : Fin m // row ∈ rows} //
            0 < support.card},
        Fintype.card
            (V13RealLinearNoTargetSequentialPrefixPinnedSupportMapClass
              i₀ observer t pref row₁ support.val) *
          M ≤ 4 * N := by
    intro support
    rcases Finset.card_pos.mp support.property with ⟨row₀, hrow₀⟩
    simpa [M, N, rows] using
      v13RealLinearNoTargetSequentialPrefixPinnedSupportMapClass_card_mul_two_pow_le_prefixMapClass
        i₀ observer t pref hrow₁ row₀ hrow₀
  have hSigma :
      Fintype.card Sigma * M ≤ 4 * 2 ^ rows.card * N := by
    have hcardSigma :
        Fintype.card Sigma =
          ∑ support :
              {support : Finset {row : Fin m // row ∈ rows} //
                0 < support.card},
            Fintype.card
              (V13RealLinearNoTargetSequentialPrefixPinnedSupportMapClass
                i₀ observer t pref row₁ support.val) := by
      dsimp [Sigma, V13RealLinearNoTargetSequentialPrefixHitSupportSigma, rows]
      exact Fintype.card_sigma
    rw [hcardSigma]
    rw [Finset.sum_mul]
    calc
      (∑ support :
          {support : Finset {row : Fin m // row ∈ rows} //
            0 < support.card},
          Fintype.card
              (V13RealLinearNoTargetSequentialPrefixPinnedSupportMapClass
                i₀ observer t pref row₁ support.val) *
            M) ≤
          ∑ _support :
              {support : Finset {row : Fin m // row ∈ rows} //
                0 < support.card}, 4 * N := by
            apply Finset.sum_le_sum
            intro support _hsupport
            exact hterm support
      _ =
          Fintype.card
              {support : Finset {row : Fin m // row ∈ rows} //
                0 < support.card} *
            (4 * N) := by
        rw [Finset.sum_const]
        simp
      _ ≤ 2 ^ rows.card * (4 * N) := by
        exact Nat.mul_le_mul_right (4 * N) hSupportLe
      _ = 4 * 2 ^ rows.card * N := by ring
  calc
    Fintype.card Hit * M ≤ Fintype.card Sigma * M :=
      Nat.mul_le_mul_right M hHitLe
    _ ≤ 4 * 2 ^ rows.card * N := hSigma
    _ =
      4 * 2 ^ (v13RealLinearSequentialPrefixTranscriptVectorRows pref).card *
        Fintype.card
          (V13RealLinearNoTargetSequentialPrefixMapClass
            i₀ observer t pref) := by
        simp [rows, N]

noncomputable def
    v13RealLinearSequentialPrefixTranscriptVectorRowsTranscript
    {m n : Nat}
    (pref : V13RealLinearSequentialPrefixTranscriptVector m n) :
    V13RealLinearRowsTranscriptSpace m
      (v13RealLinearSequentialPrefixTranscriptVectorRows pref) :=
  fun row =>
    v13RealLinearSequentialPrefixTranscriptVectorRowView pref row

noncomputable def
    v13RealLinearSequentialPrefixTranscriptVectorCompletion
    {m n : Nat}
    (pref : V13RealLinearSequentialPrefixTranscriptVector m n)
    (assignment :
      V13RealLinearRowsUnreadAssignment m
        (v13RealLinearSequentialPrefixTranscriptVectorRows pref)) :
    F2Vec m :=
  v13RealLinearRowsTranscriptCompletion
    (v13RealLinearSequentialPrefixTranscriptVectorRowsTranscript pref)
    assignment

noncomputable def
    v13RealLinearNoTargetSequentialPrefixMapClassCompletedVector
    {m q : Nat} {i₀ : Fin m}
    {observer : V13RealLinearSequentialRowObserver m q} {t : Fin q}
    {pref :
      V13RealLinearSequentialPrefixTranscriptVector m (t : Nat)}
    (A :
      V13RealLinearNoTargetSequentialPrefixMapClass
        i₀ observer t pref)
    (assignment :
      V13RealLinearRowsUnreadAssignment m
        (v13RealLinearSequentialPrefixTranscriptVectorRows pref)) :
    F2Vec m :=
  A.val.val.toEquiv.symm
    (v13RealLinearSequentialPrefixTranscriptVectorCompletion
      pref assignment)

theorem
    v13RealLinearNoTargetSequentialPrefixWorldSet_rowView_eq
    {m q : Nat} {i₀ : Fin m}
    {observer : V13RealLinearSequentialRowObserver m q} {t : Fin q}
    {pref :
      V13RealLinearSequentialPrefixTranscriptVector m (t : Nat)}
    (omega :
      V13RealLinearNoTargetSequentialPrefixWorldSet
        i₀ observer t pref)
    (row :
      {row : Fin m //
        row ∈ v13RealLinearSequentialPrefixTranscriptVectorRows pref}) :
    v13RealLinearSequentialPrefixTranscriptVectorRowView pref row =
      v13RealLinearRowView row.1
        (v13RealLinearPublicInput
          ({ x := omega.val.2, A := omega.val.1.val } :
            V13RealLinearWorld m)) := by
  classical
  rcases
      v13RealLinearSequentialPrefixTranscriptVectorRowView_spec pref row with
    ⟨entry, hentry, hentryRow, hrowView⟩
  have hlist :
      v13RealLinearSequentialPrefixTranscriptVectorToList pref =
        v13RealLinearSequentialRowPrefixTranscriptOf observer
          (v13RealLinearPublicInput
            ({ x := omega.val.2, A := omega.val.1.val } :
              V13RealLinearWorld m))
          (t : Nat) := by
    have h :=
      congrArg v13RealLinearSequentialPrefixTranscriptVectorToList
        omega.property.symm
    simpa [v13RealLinearSequentialPrefixTranscriptVectorOf_toList]
      using h
  have hentryActual :
      entry ∈
        v13RealLinearSequentialRowPrefixTranscriptOf observer
          (v13RealLinearPublicInput
            ({ x := omega.val.2, A := omega.val.1.val } :
              V13RealLinearWorld m))
          (t : Nat) := by
    simpa [hlist] using hentry
  have hviewActual :=
    v13RealLinearSequentialRowPrefixTranscriptOf_mem_view
      observer
      (v13RealLinearPublicInput
        ({ x := omega.val.2, A := omega.val.1.val } :
          V13RealLinearWorld m))
      (t : Nat) hentryActual
  calc
    v13RealLinearSequentialPrefixTranscriptVectorRowView pref row =
        entry.2 := hrowView
    _ =
        v13RealLinearRowView entry.1
          (v13RealLinearPublicInput
            ({ x := omega.val.2, A := omega.val.1.val } :
              V13RealLinearWorld m)) := hviewActual
    _ =
        v13RealLinearRowView row.1
          (v13RealLinearPublicInput
            ({ x := omega.val.2, A := omega.val.1.val } :
              V13RealLinearWorld m)) := by
          rw [hentryRow]

theorem
    v13RealLinearNoTargetSequentialPrefixWorldSet_prefixRows_eq
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (pref :
      V13RealLinearSequentialPrefixTranscriptVector m (t : Nat))
    (omega :
      V13RealLinearNoTargetSequentialPrefixWorldSet
        i₀ observer t pref) :
    v13RealLinearRowTracePrefixRows
        (v13RealLinearNoTargetRowsSequentialQRowTrace i₀ observer omega.val)
        (t : Nat) =
      v13RealLinearSequentialPrefixTranscriptVectorRows pref := by
  classical
  let publicInput :=
    v13RealLinearPublicInput
      ({ x := omega.val.2, A := omega.val.1.val } : V13RealLinearWorld m)
  have htraceRows :
      v13RealLinearRowTracePrefixRows
          (v13RealLinearNoTargetRowsSequentialQRowTrace i₀ observer omega.val)
          (t : Nat) =
        v13RealLinearSequentialRowTranscriptRows
          (v13RealLinearSequentialRowPrefixTranscriptOf
            observer publicInput (t : Nat)) := by
    simpa [v13RealLinearNoTargetRowsSequentialQRowTrace, publicInput] using
      (v13RealLinearSequentialRowTracePrefixRows_eq_prefixTranscriptRows
        observer publicInput (Nat.le_of_lt t.isLt))
  have hvectorRows :
      v13RealLinearSequentialPrefixTranscriptVectorRows
          (v13RealLinearSequentialPrefixTranscriptVectorOf observer
            publicInput (t : Nat)) =
        v13RealLinearSequentialRowTranscriptRows
          (v13RealLinearSequentialRowPrefixTranscriptOf
            observer publicInput (t : Nat)) :=
    v13RealLinearSequentialPrefixTranscriptVectorOf_rows
      observer publicInput (t : Nat)
  calc
    v13RealLinearRowTracePrefixRows
        (v13RealLinearNoTargetRowsSequentialQRowTrace i₀ observer omega.val)
        (t : Nat) =
      v13RealLinearSequentialRowTranscriptRows
        (v13RealLinearSequentialRowPrefixTranscriptOf
          observer publicInput (t : Nat)) := htraceRows
    _ =
      v13RealLinearSequentialPrefixTranscriptVectorRows
        (v13RealLinearSequentialPrefixTranscriptVectorOf observer
          publicInput (t : Nat)) := hvectorRows.symm
    _ = v13RealLinearSequentialPrefixTranscriptVectorRows pref := by
      rw [omega.property]

theorem
    v13RealLinearNoTargetSequentialPrefixWorldSet_nextRow_eq
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (pref :
      V13RealLinearSequentialPrefixTranscriptVector m (t : Nat))
    (omega :
      V13RealLinearNoTargetSequentialPrefixWorldSet
        i₀ observer t pref) :
    ∃ h : (t : Nat) <
        (v13RealLinearNoTargetRowsSequentialQRowTrace i₀ observer omega.val).length,
      (v13RealLinearNoTargetRowsSequentialQRowTrace i₀ observer omega.val).get
          ⟨(t : Nat), h⟩ =
        v13RealLinearSequentialPrefixTranscriptVectorNextRow observer pref := by
  classical
  let publicInput :=
    v13RealLinearPublicInput
      ({ x := omega.val.2, A := omega.val.1.val } : V13RealLinearWorld m)
  have hlen : (t : Nat) <
      (v13RealLinearNoTargetRowsSequentialQRowTrace
        i₀ observer omega.val).length := by
    simp [v13RealLinearNoTargetRowsSequentialQRowTrace,
      v13RealLinearSequentialRowTraceOf_length]
  refine ⟨hlen, ?_⟩
  have hget :
      (v13RealLinearNoTargetRowsSequentialQRowTrace
          i₀ observer omega.val).get ⟨(t : Nat), hlen⟩ =
        observer.chooseRow
          (v13RealLinearSequentialRowPrefixTranscriptOf
            observer publicInput (t : Nat)) := by
    simpa [v13RealLinearNoTargetRowsSequentialQRowTrace, publicInput] using
      (v13RealLinearSequentialRowTraceOf_get_eq_chooseRow
        observer publicInput t.isLt)
  have hnext :
      v13RealLinearSequentialPrefixTranscriptVectorNextRow observer
          (v13RealLinearSequentialPrefixTranscriptVectorOf observer
            publicInput (t : Nat)) =
        observer.chooseRow
          (v13RealLinearSequentialRowPrefixTranscriptOf
            observer publicInput (t : Nat)) :=
    v13RealLinearSequentialPrefixTranscriptVectorOf_nextRow
      observer publicInput (t : Nat)
  calc
    (v13RealLinearNoTargetRowsSequentialQRowTrace
        i₀ observer omega.val).get ⟨(t : Nat), hlen⟩ =
      observer.chooseRow
        (v13RealLinearSequentialRowPrefixTranscriptOf
          observer publicInput (t : Nat)) := hget
    _ =
      v13RealLinearSequentialPrefixTranscriptVectorNextRow observer
        (v13RealLinearSequentialPrefixTranscriptVectorOf observer
          publicInput (t : Nat)) := hnext.symm
    _ = v13RealLinearSequentialPrefixTranscriptVectorNextRow observer pref := by
      rw [omega.property]

noncomputable def
    v13RealLinearNoTargetSequentialPrefixWorldSetToOrderedPrefixHitOfNextRowMemOfPrefixRowsGenerateTarget
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (pref :
      V13RealLinearSequentialPrefixTranscriptVector m (t : Nat))
    (omega :
      V13RealLinearNoTargetSequentialPrefixWorldSet
        i₀ observer t pref)
    (hmem :
      v13RealLinearSequentialPrefixTranscriptVectorNextRow observer pref ∈
        v13RealLinearSequentialPrefixTranscriptVectorRows pref)
    (hgen :
      V13RealLinearRowsGenerateTarget omega.val.1.val
        (v13RealLinearSequentialPrefixTranscriptVectorRows pref) i₀) :
    V13RealLinearNoTargetSequentialTraceFirstCosetHitOrderedPrefixWorldSet
      i₀ observer t pref := by
  classical
  let trace :=
    v13RealLinearNoTargetRowsSequentialQRowTrace i₀ observer omega.val
  let publicInput :=
    v13RealLinearPublicInput
      ({ x := omega.val.2, A := omega.val.1.val } : V13RealLinearWorld m)
  have hlen : (t : Nat) < trace.length := by
    simp [trace, v13RealLinearNoTargetRowsSequentialQRowTrace,
      v13RealLinearSequentialRowTraceOf_length]
  have hget :
      trace.get ⟨(t : Nat), hlen⟩ =
        v13RealLinearSequentialPrefixTranscriptVectorNextRow observer
          pref := by
    have hgetChoose :
        trace.get ⟨(t : Nat), hlen⟩ =
          observer.chooseRow
            (v13RealLinearSequentialRowPrefixTranscriptOf
              observer publicInput (t : Nat)) := by
      simpa [trace, v13RealLinearNoTargetRowsSequentialQRowTrace,
        publicInput] using
        (v13RealLinearSequentialRowTraceOf_get_eq_chooseRow
          observer publicInput t.isLt)
    have hnext :
        v13RealLinearSequentialPrefixTranscriptVectorNextRow observer
            (v13RealLinearSequentialPrefixTranscriptVectorOf observer
              publicInput (t : Nat)) =
          observer.chooseRow
            (v13RealLinearSequentialRowPrefixTranscriptOf
              observer publicInput (t : Nat)) :=
      v13RealLinearSequentialPrefixTranscriptVectorOf_nextRow
        observer publicInput (t : Nat)
    calc
      trace.get ⟨(t : Nat), hlen⟩ =
        observer.chooseRow
          (v13RealLinearSequentialRowPrefixTranscriptOf
            observer publicInput (t : Nat)) := hgetChoose
      _ =
        v13RealLinearSequentialPrefixTranscriptVectorNextRow observer
          (v13RealLinearSequentialPrefixTranscriptVectorOf observer
            publicInput (t : Nat)) := hnext.symm
      _ = v13RealLinearSequentialPrefixTranscriptVectorNextRow observer pref := by
        rw [omega.property]
  have hrows :=
    v13RealLinearNoTargetSequentialPrefixWorldSet_prefixRows_eq
      i₀ observer t pref omega
  have hrowHit :
      V13RealLinearRowFunctionalTargetCosetHit omega.val.1.val
        (v13RealLinearSequentialPrefixTranscriptVectorRows pref) i₀
        (v13RealLinearSequentialPrefixTranscriptVectorNextRow observer
          pref) :=
    v13RealLinear_rowFunctionalTargetCosetHit_of_rowsGenerateTarget_of_mem
      omega.val.1.val i₀
      (v13RealLinearSequentialPrefixTranscriptVectorNextRow observer pref)
      hmem hgen
  have hrowHitTrace :
      V13RealLinearRowFunctionalTargetCosetHit omega.val.1.val
        (v13RealLinearRowTracePrefixRows trace (t : Nat)) i₀
        (trace.get ⟨(t : Nat), hlen⟩) := by
    rw [hrows, hget]
    exact hrowHit
  have htraceHit :
      V13RealLinearRowTraceCosetHit omega.val.1.val i₀ trace (t : Nat) :=
    ⟨hlen, hrowHitTrace⟩
  have hfirst :
      V13RealLinearAdaptiveQRowTraceFirstCosetHit
        (v13RealLinearNoTargetRowsSequentialQRowExperiment i₀ observer)
        i₀
        (v13RealLinearNoTargetRowsSequentialQRowTrace i₀ observer)
        t omega.val := by
    refine ⟨by simpa [trace] using hlen, ?_⟩
    simpa [trace, v13RealLinearNoTargetRowsSequentialQRowExperiment,
      v13RealLinearNoTargetRowsCausalQRowExperiment,
      v13RealLinearNoTargetRowsQRowExperiment] using htraceHit
  exact ⟨⟨omega.val, hfirst⟩, omega.property⟩

theorem
    v13RealLinearNoTargetSequentialPrefixWorldSet_orderedPrefixHit_nonempty_of_nextRow_mem_of_prefixRowsGenerateTarget
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (pref :
      V13RealLinearSequentialPrefixTranscriptVector m (t : Nat))
    (omega :
      V13RealLinearNoTargetSequentialPrefixWorldSet
        i₀ observer t pref)
    (hmem :
      v13RealLinearSequentialPrefixTranscriptVectorNextRow observer pref ∈
        v13RealLinearSequentialPrefixTranscriptVectorRows pref)
    (hgen :
      V13RealLinearRowsGenerateTarget omega.val.1.val
        (v13RealLinearSequentialPrefixTranscriptVectorRows pref) i₀) :
    Nonempty
      (V13RealLinearNoTargetSequentialTraceFirstCosetHitOrderedPrefixWorldSet
        i₀ observer t pref) :=
  ⟨v13RealLinearNoTargetSequentialPrefixWorldSetToOrderedPrefixHitOfNextRowMemOfPrefixRowsGenerateTarget
    i₀ observer t pref omega hmem hgen⟩

noncomputable def
    v13RealLinearNoTargetSequentialPrefixMapClassTimesUnreadAssignmentToPrefixWorldSet
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (pref :
      V13RealLinearSequentialPrefixTranscriptVector m (t : Nat)) :
    (V13RealLinearNoTargetSequentialPrefixMapClass i₀ observer t pref ×
      V13RealLinearRowsUnreadAssignment m
        (v13RealLinearSequentialPrefixTranscriptVectorRows pref)) ↪
      V13RealLinearNoTargetSequentialPrefixWorldSet
        i₀ observer t pref where
  toFun cell := by
    classical
    let A := cell.1
    let assignment := cell.2
    let z :=
      v13RealLinearNoTargetSequentialPrefixMapClassCompletedVector
        A assignment
    let publicW :=
      v13RealLinearPublicInput
        ({ x := v13RealLinearNoTargetSequentialPrefixMapClassWitness A,
           A := A.val.val } : V13RealLinearWorld m)
    let publicZ :=
      v13RealLinearPublicInput
        ({ x := z, A := A.val.val } : V13RealLinearWorld m)
    have hprefixZ :
        v13RealLinearSequentialPrefixTranscriptVectorOf observer
            publicZ (t : Nat) =
          pref := by
      apply
        v13RealLinearSequentialPrefixTranscriptVectorOf_eq_of_rowView_eq_on_rows
          observer
          (v13RealLinearNoTargetSequentialPrefixMapClassWitness_property A)
      intro row hrow
      have hleft :
          A.val.val.toEquiv z row =
            (v13RealLinearSequentialPrefixTranscriptVectorRowView
              pref ⟨row, hrow⟩).2 := by
        calc
          A.val.val.toEquiv z row =
              v13RealLinearSequentialPrefixTranscriptVectorCompletion
                pref assignment row := by
                simp [z,
                  v13RealLinearNoTargetSequentialPrefixMapClassCompletedVector]
          _ =
              (v13RealLinearSequentialPrefixTranscriptVectorRowView
                pref ⟨row, hrow⟩).2 :=
                v13RealLinearRowsTranscriptCompletion_of_mem
                  (v13RealLinearSequentialPrefixTranscriptVectorRowsTranscript
                    pref)
                  assignment hrow
      have hright :
          A.val.val.toEquiv
              (v13RealLinearNoTargetSequentialPrefixMapClassWitness A)
              row =
            (v13RealLinearSequentialPrefixTranscriptVectorRowView
              pref ⟨row, hrow⟩).2 := by
        have hview :=
          v13RealLinearNoTargetSequentialPrefixMapClass_rowView_eq
            A ⟨row, hrow⟩
        simpa [v13RealLinearRowView, v13RealLinearPublicInput] using
          (congrArg Prod.snd hview).symm
      exact
        v13RealLinearRowView_eq_of_A_eq_rhs_eq
          (public₀ := publicZ) (public₁ := publicW) (row := row)
          rfl (hleft.trans hright.symm)
    exact ⟨(A.val, z), hprefixZ⟩
  inj' := by
    classical
    intro cell₀ cell₁ hcell
    apply Prod.ext
    · apply Subtype.ext
      exact
        congrArg
          (fun omega :
            V13RealLinearNoTargetSequentialPrefixWorldSet
              i₀ observer t pref => omega.val.1)
          hcell
    · have hA :
          cell₀.1 = cell₁.1 := by
        apply Subtype.ext
        exact
          congrArg
            (fun omega :
              V13RealLinearNoTargetSequentialPrefixWorldSet
                i₀ observer t pref => omega.val.1)
            hcell
      funext row
      have hz :
          v13RealLinearNoTargetSequentialPrefixMapClassCompletedVector
              cell₀.1 cell₀.2 =
            v13RealLinearNoTargetSequentialPrefixMapClassCompletedVector
              cell₁.1 cell₁.2 := by
        simpa using
            congrArg
              (fun omega :
                V13RealLinearNoTargetSequentialPrefixWorldSet
                  i₀ observer t pref => omega.val.2)
              hcell
      have hbraw :=
        congrFun (congrArg cell₀.1.val.val.toEquiv hz) row.1
      have hb :
          v13RealLinearSequentialPrefixTranscriptVectorCompletion
              pref cell₀.2 row.1 =
            v13RealLinearSequentialPrefixTranscriptVectorCompletion
              pref cell₁.2 row.1 := by
        simpa [
          v13RealLinearNoTargetSequentialPrefixMapClassCompletedVector,
          v13RealLinearSequentialPrefixTranscriptVectorCompletion, hA] using hbraw
      calc
        cell₀.2 row =
            v13RealLinearSequentialPrefixTranscriptVectorCompletion
              pref cell₀.2 row.1 := by
              exact
                (v13RealLinearRowsTranscriptCompletion_of_not_mem
                  (v13RealLinearSequentialPrefixTranscriptVectorRowsTranscript
                    pref)
                  cell₀.2 row).symm
        _ =
            v13RealLinearSequentialPrefixTranscriptVectorCompletion
              pref cell₁.2 row.1 := hb
        _ = cell₁.2 row :=
              v13RealLinearRowsTranscriptCompletion_of_not_mem
                (v13RealLinearSequentialPrefixTranscriptVectorRowsTranscript
                  pref)
                cell₁.2 row

theorem
    v13RealLinearNoTargetSequentialPrefixMapClass_card_mul_unread_le_prefixWorldSet
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (pref :
      V13RealLinearSequentialPrefixTranscriptVector m (t : Nat)) :
    Fintype.card
        (V13RealLinearNoTargetSequentialPrefixMapClass
          i₀ observer t pref) *
      2 ^ (m -
        (v13RealLinearSequentialPrefixTranscriptVectorRows pref).card) ≤
    Fintype.card
        (V13RealLinearNoTargetSequentialPrefixWorldSet
          i₀ observer t pref) := by
  classical
  let rows := v13RealLinearSequentialPrefixTranscriptVectorRows pref
  have hle :
      Fintype.card
          (V13RealLinearNoTargetSequentialPrefixMapClass
            i₀ observer t pref ×
            V13RealLinearRowsUnreadAssignment m rows) ≤
        Fintype.card
          (V13RealLinearNoTargetSequentialPrefixWorldSet
            i₀ observer t pref) :=
    Fintype.card_le_of_embedding
      (v13RealLinearNoTargetSequentialPrefixMapClassTimesUnreadAssignmentToPrefixWorldSet
        i₀ observer t pref)
  simpa [rows, Fintype.card_prod,
    v13RealLinearRowsUnreadAssignment_card] using hle

noncomputable def
    v13RealLinearNoTargetSequentialWorldEquivSigmaPrefixWorldSet
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q) :
    V13RealLinearAdaptiveQRowWorld m
        (V13RealLinearNoTargetRowsMap m i₀) ≃
      (Σ pref :
        V13RealLinearSequentialPrefixTranscriptVector m (t : Nat),
        V13RealLinearNoTargetSequentialPrefixWorldSet
          i₀ observer t pref) where
  toFun omega := by
    let pref :=
      v13RealLinearSequentialPrefixTranscriptVectorOf observer
        (v13RealLinearPublicInput
          ({ x := omega.2, A := omega.1.val } : V13RealLinearWorld m))
        (t : Nat)
    exact ⟨pref, ⟨omega, rfl⟩⟩
  invFun cell := cell.2.val
  left_inv _omega := rfl
  right_inv cell := by
    rcases cell with ⟨pref, omega, hpref⟩
    dsimp
    cases hpref
    rfl

theorem
    v13RealLinearNoTargetSequentialPrefixWorldSet_sum_card_eq_world
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q) :
    (∑ pref :
        V13RealLinearSequentialPrefixTranscriptVector m (t : Nat),
      Fintype.card
        (V13RealLinearNoTargetSequentialPrefixWorldSet
          i₀ observer t pref)) =
      Fintype.card
        (V13RealLinearAdaptiveQRowWorld m
          (V13RealLinearNoTargetRowsMap m i₀)) := by
  classical
  calc
    (∑ pref :
        V13RealLinearSequentialPrefixTranscriptVector m (t : Nat),
      Fintype.card
        (V13RealLinearNoTargetSequentialPrefixWorldSet
          i₀ observer t pref)) =
        Fintype.card
          (Σ pref :
            V13RealLinearSequentialPrefixTranscriptVector m (t : Nat),
            V13RealLinearNoTargetSequentialPrefixWorldSet
              i₀ observer t pref) := by
          rw [Fintype.card_sigma]
    _ =
        Fintype.card
          (V13RealLinearAdaptiveQRowWorld m
            (V13RealLinearNoTargetRowsMap m i₀)) := by
          exact
            (Fintype.card_congr
              (v13RealLinearNoTargetSequentialWorldEquivSigmaPrefixWorldSet
                i₀ observer t)).symm

theorem
    v13RealLinearNoTargetSequentialTraceFirstCosetHitOrderedPrefixWorldSet_prefixRows_eq
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (pref :
      V13RealLinearSequentialPrefixTranscriptVector m (t : Nat))
    (omega :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitOrderedPrefixWorldSet
        i₀ observer t pref) :
    v13RealLinearRowTracePrefixRows
        (v13RealLinearNoTargetRowsSequentialQRowTrace
          i₀ observer omega.val.val)
        (t : Nat) =
      v13RealLinearSequentialPrefixTranscriptVectorRows pref := by
  classical
  let publicInput :=
    v13RealLinearPublicInput
      ({ x := omega.val.val.2, A := omega.val.val.1.val } :
        V13RealLinearWorld m)
  have htraceRows :
      v13RealLinearRowTracePrefixRows
          (v13RealLinearNoTargetRowsSequentialQRowTrace
            i₀ observer omega.val.val)
          (t : Nat) =
        v13RealLinearSequentialRowTranscriptRows
          (v13RealLinearSequentialRowPrefixTranscriptOf
            observer publicInput (t : Nat)) := by
    simpa [v13RealLinearNoTargetRowsSequentialQRowTrace, publicInput] using
      (v13RealLinearSequentialRowTracePrefixRows_eq_prefixTranscriptRows
        observer publicInput (Nat.le_of_lt t.isLt))
  have hvectorRows :
      v13RealLinearSequentialPrefixTranscriptVectorRows
          (v13RealLinearSequentialPrefixTranscriptVectorOf observer
            publicInput (t : Nat)) =
        v13RealLinearSequentialRowTranscriptRows
          (v13RealLinearSequentialRowPrefixTranscriptOf
            observer publicInput (t : Nat)) :=
    v13RealLinearSequentialPrefixTranscriptVectorOf_rows
      observer publicInput (t : Nat)
  calc
    v13RealLinearRowTracePrefixRows
        (v13RealLinearNoTargetRowsSequentialQRowTrace
          i₀ observer omega.val.val)
        (t : Nat) =
      v13RealLinearSequentialRowTranscriptRows
        (v13RealLinearSequentialRowPrefixTranscriptOf
          observer publicInput (t : Nat)) := htraceRows
    _ =
      v13RealLinearSequentialPrefixTranscriptVectorRows
        (v13RealLinearSequentialPrefixTranscriptVectorOf observer
          publicInput (t : Nat)) := hvectorRows.symm
    _ = v13RealLinearSequentialPrefixTranscriptVectorRows pref := by
      rw [omega.property]

theorem
    v13RealLinearNoTargetSequentialTraceFirstCosetHitOrderedPrefixWorldSet_hitRow_eq
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (pref :
      V13RealLinearSequentialPrefixTranscriptVector m (t : Nat))
    (omega :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitOrderedPrefixWorldSet
        i₀ observer t pref) :
    ∃ h : (t : Nat) <
        (v13RealLinearNoTargetRowsSequentialQRowTrace
          i₀ observer omega.val.val).length,
      (v13RealLinearNoTargetRowsSequentialQRowTrace
          i₀ observer omega.val.val).get ⟨(t : Nat), h⟩ =
        v13RealLinearSequentialPrefixTranscriptVectorNextRow observer pref := by
  classical
  let publicInput :=
    v13RealLinearPublicInput
      ({ x := omega.val.val.2, A := omega.val.val.1.val } :
        V13RealLinearWorld m)
  have hlen : (t : Nat) <
      (v13RealLinearNoTargetRowsSequentialQRowTrace
        i₀ observer omega.val.val).length := by
    simp [v13RealLinearNoTargetRowsSequentialQRowTrace,
      v13RealLinearSequentialRowTraceOf_length]
  refine ⟨hlen, ?_⟩
  have hget :
      (v13RealLinearNoTargetRowsSequentialQRowTrace
          i₀ observer omega.val.val).get ⟨(t : Nat), hlen⟩ =
        observer.chooseRow
          (v13RealLinearSequentialRowPrefixTranscriptOf
            observer publicInput (t : Nat)) := by
    simpa [v13RealLinearNoTargetRowsSequentialQRowTrace, publicInput] using
      (v13RealLinearSequentialRowTraceOf_get_eq_chooseRow
        observer publicInput t.isLt)
  have hnext :
      v13RealLinearSequentialPrefixTranscriptVectorNextRow observer
          (v13RealLinearSequentialPrefixTranscriptVectorOf observer
            publicInput (t : Nat)) =
        observer.chooseRow
          (v13RealLinearSequentialRowPrefixTranscriptOf
            observer publicInput (t : Nat)) :=
    v13RealLinearSequentialPrefixTranscriptVectorOf_nextRow
      observer publicInput (t : Nat)
  calc
    (v13RealLinearNoTargetRowsSequentialQRowTrace
        i₀ observer omega.val.val).get ⟨(t : Nat), hlen⟩ =
      observer.chooseRow
        (v13RealLinearSequentialRowPrefixTranscriptOf
          observer publicInput (t : Nat)) := hget
    _ =
      v13RealLinearSequentialPrefixTranscriptVectorNextRow observer
        (v13RealLinearSequentialPrefixTranscriptVectorOf observer
          publicInput (t : Nat)) := hnext.symm
    _ = v13RealLinearSequentialPrefixTranscriptVectorNextRow observer pref := by
      rw [omega.property]

theorem
    v13RealLinearNoTargetSequentialTraceFirstCosetHitOrderedPrefixWorldSet_cosetHit
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (pref :
      V13RealLinearSequentialPrefixTranscriptVector m (t : Nat))
    (omega :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitOrderedPrefixWorldSet
        i₀ observer t pref) :
    V13RealLinearRowFunctionalTargetCosetHit omega.val.val.1.val
      (v13RealLinearSequentialPrefixTranscriptVectorRows pref) i₀
      (v13RealLinearSequentialPrefixTranscriptVectorNextRow observer
        pref) := by
  classical
  let rows := v13RealLinearSequentialPrefixTranscriptVectorRows pref
  let row₁ := v13RealLinearSequentialPrefixTranscriptVectorNextRow observer pref
  let trace :=
    v13RealLinearNoTargetRowsSequentialQRowTrace i₀ observer omega.val.val
  rcases omega.val.property with ⟨_hlenHit, hhit⟩
  rcases
      v13RealLinearNoTargetSequentialTraceFirstCosetHitOrderedPrefixWorldSet_hitRow_eq
        i₀ observer t pref omega with
    ⟨hrowIndex, hget⟩
  rcases hhit with ⟨hhitIndex, hhitRows⟩
  have hidx :
      (⟨(t : Nat), hhitIndex⟩ : Fin trace.length) =
        ⟨(t : Nat), hrowIndex⟩ := by
    apply Fin.ext
    rfl
  have hrows :=
    v13RealLinearNoTargetSequentialTraceFirstCosetHitOrderedPrefixWorldSet_prefixRows_eq
      i₀ observer t pref omega
  have hhitRows' :
      V13RealLinearRowFunctionalTargetCosetHit omega.val.val.1.val
        rows i₀ (trace.get ⟨(t : Nat), hhitIndex⟩) := by
    simpa [trace, rows, hrows,
      v13RealLinearNoTargetRowsSequentialQRowExperiment,
      v13RealLinearNoTargetRowsCausalQRowExperiment,
      v13RealLinearNoTargetRowsQRowExperiment] using hhitRows
  have hgetHit :
      trace.get ⟨(t : Nat), hhitIndex⟩ = row₁ := by
    simpa [trace, row₁, hidx] using hget
  rw [hgetHit] at hhitRows'
  simpa [rows, row₁] using hhitRows'

theorem
    v13RealLinearNoTargetSequentialTraceFirstCosetHitOrderedPrefixWorldSet_prefixRowsGenerateTarget_of_nextRow_mem
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (pref :
      V13RealLinearSequentialPrefixTranscriptVector m (t : Nat))
    (omega :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitOrderedPrefixWorldSet
        i₀ observer t pref)
    (hmem :
      v13RealLinearSequentialPrefixTranscriptVectorNextRow observer pref ∈
        v13RealLinearSequentialPrefixTranscriptVectorRows pref) :
    V13RealLinearRowsGenerateTarget omega.val.val.1.val
      (v13RealLinearSequentialPrefixTranscriptVectorRows pref) i₀ := by
  exact
    v13RealLinear_rowsGenerateTarget_of_rowFunctionalTargetCosetHit_of_mem
      omega.val.val.1.val i₀
      (v13RealLinearSequentialPrefixTranscriptVectorNextRow observer pref)
      hmem
      (v13RealLinearNoTargetSequentialTraceFirstCosetHitOrderedPrefixWorldSet_cosetHit
        i₀ observer t pref omega)

theorem
    v13RealLinearNoTargetSequentialTraceFirstCosetHitOrderedPrefixWorldSet_priorCosetHit_of_nextRow_mem
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (pref :
      V13RealLinearSequentialPrefixTranscriptVector m (t : Nat))
    (omega :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitOrderedPrefixWorldSet
        i₀ observer t pref)
    (hmem :
      v13RealLinearSequentialPrefixTranscriptVectorNextRow observer pref ∈
        v13RealLinearSequentialPrefixTranscriptVectorRows pref) :
    ∃ s : Fin (t : Nat),
      V13RealLinearRowTraceCosetHit omega.val.val.1.val i₀
        (v13RealLinearNoTargetRowsSequentialQRowTrace
          i₀ observer omega.val.val) s := by
  classical
  let trace :=
    v13RealLinearNoTargetRowsSequentialQRowTrace i₀ observer omega.val.val
  have hrows :=
    v13RealLinearNoTargetSequentialTraceFirstCosetHitOrderedPrefixWorldSet_prefixRows_eq
      i₀ observer t pref omega
  have hgenPref :=
    v13RealLinearNoTargetSequentialTraceFirstCosetHitOrderedPrefixWorldSet_prefixRowsGenerateTarget_of_nextRow_mem
      i₀ observer t pref omega hmem
  have hgenTrace :
      V13RealLinearRowsGenerateTarget omega.val.val.1.val
        (v13RealLinearRowTracePrefixRows trace (t : Nat)) i₀ := by
    simpa [trace, hrows] using hgenPref
  rcases
      v13RealLinearRowTraceNewCapture_exists_lt_of_prefixRowsGenerateTarget
        omega.val.val.1.val i₀ trace
        (Nat.le_of_lt omega.val.property.1) hgenTrace with
    ⟨s, hsnew⟩
  exact
    ⟨s,
      v13RealLinearRowTraceCosetHit_of_newCapture
        omega.val.val.1.val i₀ trace
        (lt_trans s.isLt omega.val.property.1) hsnew⟩

/-- L0 freshness bridge for conditioned ordered-prefix counting.  It states
that every counted ordered-prefix hit reads a row outside the realized prefix
rowset.  This is exactly the first-hit/freshness step needed before the
conditioned shear count can act on the next row. -/
def
    V13RealLinearNoTargetRowsSequentialTraceCosetHitOrderedPrefixFreshnessBridge
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) : Prop :=
  ∀ t : Fin q,
    ∀ pref :
      V13RealLinearSequentialPrefixTranscriptVector m (t : Nat),
    ∀ _omega :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitOrderedPrefixWorldSet
        i₀ observer t pref,
      v13RealLinearSequentialPrefixTranscriptVectorNextRow observer pref ∉
        v13RealLinearSequentialPrefixTranscriptVectorRows pref

/-- No-prior-hit bridge for the current step-indexed hit surface.  The present
`TraceFirstCosetHit` event records a hit at step `t`; this bridge is the
additional data that makes that hit a true first hit. -/
def
    V13RealLinearNoTargetRowsSequentialTraceCosetHitNoPriorBridge
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) : Prop :=
  ∀ t : Fin q,
    ∀ omega :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitWorldSet
        i₀ observer t,
    ∀ s : Fin (t : Nat),
      ¬ V13RealLinearRowTraceCosetHit omega.val.1.val i₀
        (v13RealLinearNoTargetRowsSequentialQRowTrace i₀ observer omega.val) s

theorem
    v13RealLinearNoTargetSequentialTraceFirstCosetHitOrderedPrefixWorldSet_hitRow_not_mem_of_noPrior
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (pref :
      V13RealLinearSequentialPrefixTranscriptVector m (t : Nat))
    (omega :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitOrderedPrefixWorldSet
        i₀ observer t pref)
    (hprior :
      ∀ s : Fin (t : Nat),
        ¬ V13RealLinearRowTraceCosetHit omega.val.val.1.val i₀
          (v13RealLinearNoTargetRowsSequentialQRowTrace
            i₀ observer omega.val.val) s) :
    v13RealLinearSequentialPrefixTranscriptVectorNextRow observer pref ∉
      v13RealLinearSequentialPrefixTranscriptVectorRows pref := by
  classical
  let trace :=
    v13RealLinearNoTargetRowsSequentialQRowTrace i₀ observer omega.val.val
  rcases
      v13RealLinearNoTargetSequentialTraceFirstCosetHitOrderedPrefixWorldSet_hitRow_eq
        i₀ observer t pref omega with
    ⟨hlen, hget⟩
  have hhit : V13RealLinearRowTraceCosetHit omega.val.val.1.val i₀
      trace (t : Nat) := by
    simpa [trace, v13RealLinearNoTargetRowsSequentialQRowExperiment,
      v13RealLinearNoTargetRowsCausalQRowExperiment,
      v13RealLinearNoTargetRowsQRowExperiment] using omega.val.property.2
  have hfresh :
      trace.get ⟨(t : Nat), hlen⟩ ∉
        v13RealLinearRowTracePrefixRows trace (t : Nat) := by
    exact
      v13RealLinearRowTraceCosetHit_get_not_mem_of_noPrior
        omega.val.val.1.val i₀ trace hprior hhit hlen
  have hrows :=
    v13RealLinearNoTargetSequentialTraceFirstCosetHitOrderedPrefixWorldSet_prefixRows_eq
      i₀ observer t pref omega
  intro hmem
  exact
    hfresh
      (by
        rw [hget, hrows]
        exact hmem)

theorem
    V13RealLinearNoTargetRowsSequentialTraceCosetHitOrderedPrefixFreshnessBridge_of_noPrior
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q)
    (hprior :
      V13RealLinearNoTargetRowsSequentialTraceCosetHitNoPriorBridge
        i₀ observer) :
    V13RealLinearNoTargetRowsSequentialTraceCosetHitOrderedPrefixFreshnessBridge
      i₀ observer := by
  intro t pref omega
  exact
    v13RealLinearNoTargetSequentialTraceFirstCosetHitOrderedPrefixWorldSet_hitRow_not_mem_of_noPrior
      i₀ observer t pref omega (hprior t omega.val)

theorem
    V13RealLinearNoTargetRowsSequentialTraceCosetHitOrderedPrefixFreshnessBridge_not_of_generated_reread_prefix
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (pref :
      V13RealLinearSequentialPrefixTranscriptVector m (t : Nat))
    (omega :
      V13RealLinearNoTargetSequentialPrefixWorldSet
        i₀ observer t pref)
    (hmem :
      v13RealLinearSequentialPrefixTranscriptVectorNextRow observer pref ∈
        v13RealLinearSequentialPrefixTranscriptVectorRows pref)
    (hgen :
      V13RealLinearRowsGenerateTarget omega.val.1.val
        (v13RealLinearSequentialPrefixTranscriptVectorRows pref) i₀) :
    ¬ V13RealLinearNoTargetRowsSequentialTraceCosetHitOrderedPrefixFreshnessBridge
      i₀ observer := by
  intro hfresh
  let hitOmega :=
    v13RealLinearNoTargetSequentialPrefixWorldSetToOrderedPrefixHitOfNextRowMemOfPrefixRowsGenerateTarget
      i₀ observer t pref omega hmem hgen
  exact hfresh t pref hitOmega hmem

theorem
    V13RealLinearNoTargetRowsSequentialTraceCosetHitNoPriorBridge_not_of_generated_reread_prefix
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (pref :
      V13RealLinearSequentialPrefixTranscriptVector m (t : Nat))
    (omega :
      V13RealLinearNoTargetSequentialPrefixWorldSet
        i₀ observer t pref)
    (hmem :
      v13RealLinearSequentialPrefixTranscriptVectorNextRow observer pref ∈
        v13RealLinearSequentialPrefixTranscriptVectorRows pref)
    (hgen :
      V13RealLinearRowsGenerateTarget omega.val.1.val
        (v13RealLinearSequentialPrefixTranscriptVectorRows pref) i₀) :
    ¬ V13RealLinearNoTargetRowsSequentialTraceCosetHitNoPriorBridge
      i₀ observer := by
  intro hprior
  let hitOmega :=
    v13RealLinearNoTargetSequentialPrefixWorldSetToOrderedPrefixHitOfNextRowMemOfPrefixRowsGenerateTarget
      i₀ observer t pref omega hmem hgen
  rcases
      v13RealLinearNoTargetSequentialTraceFirstCosetHitOrderedPrefixWorldSet_priorCosetHit_of_nextRow_mem
        i₀ observer t pref hitOmega hmem with
    ⟨s, hs⟩
  exact hprior t hitOmega.val s hs

noncomputable def
    v13RealLinearNoTargetSequentialTraceFirstCosetHitOrderedPrefixWorldSetToHitMapClassTimesUnreadAssignment
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (pref :
      V13RealLinearSequentialPrefixTranscriptVector m (t : Nat)) :
    V13RealLinearNoTargetSequentialTraceFirstCosetHitOrderedPrefixWorldSet
        i₀ observer t pref ↪
      (V13RealLinearNoTargetSequentialPrefixHitMapClass
          i₀ observer t pref
          (v13RealLinearSequentialPrefixTranscriptVectorNextRow observer
            pref) ×
        V13RealLinearRowsUnreadAssignment m
          (v13RealLinearSequentialPrefixTranscriptVectorRows pref)) where
  toFun omega := by
    classical
    let rows := v13RealLinearSequentialPrefixTranscriptVectorRows pref
    let row₁ := v13RealLinearSequentialPrefixTranscriptVectorNextRow observer pref
    let trace :=
      v13RealLinearNoTargetRowsSequentialQRowTrace i₀ observer omega.val.val
    have hcoset :
        V13RealLinearRowFunctionalTargetCosetHit omega.val.val.1.val
          rows i₀ row₁ := by
      rcases omega.val.property with ⟨_hlenHit, hhit⟩
      rcases
          v13RealLinearNoTargetSequentialTraceFirstCosetHitOrderedPrefixWorldSet_hitRow_eq
            i₀ observer t pref omega with
        ⟨hrowIndex, hget⟩
      rcases hhit with ⟨hhitIndex, hhitRows⟩
      have hidx :
          (⟨(t : Nat), hhitIndex⟩ : Fin trace.length) =
            ⟨(t : Nat), hrowIndex⟩ := by
        apply Fin.ext
        rfl
      have hrows :=
        v13RealLinearNoTargetSequentialTraceFirstCosetHitOrderedPrefixWorldSet_prefixRows_eq
          i₀ observer t pref omega
      have hhitRows' :
          V13RealLinearRowFunctionalTargetCosetHit omega.val.val.1.val
            rows i₀ (trace.get ⟨(t : Nat), hhitIndex⟩) := by
        simpa [trace, rows, hrows,
          v13RealLinearNoTargetRowsSequentialQRowExperiment,
          v13RealLinearNoTargetRowsCausalQRowExperiment,
          v13RealLinearNoTargetRowsQRowExperiment] using hhitRows
      have hgetHit :
          trace.get ⟨(t : Nat), hhitIndex⟩ = row₁ := by
        simpa [trace, row₁, hidx] using hget
      rw [hgetHit] at hhitRows'
      exact hhitRows'
    exact
      (⟨⟨omega.val.val.1, ⟨omega.val.val.2, omega.property⟩⟩,
          hcoset⟩,
        fun unread =>
          omega.val.val.1.val.toEquiv omega.val.val.2 unread.1)
  inj' := by
    classical
    intro omega₀ omega₁ h
    apply Subtype.ext
    apply Subtype.ext
    have hA :
        omega₀.val.val.1 = omega₁.val.val.1 := by
      exact
        congrArg
          (fun z :
            (V13RealLinearNoTargetSequentialPrefixHitMapClass
                i₀ observer t pref
                (v13RealLinearSequentialPrefixTranscriptVectorNextRow
                  observer pref) ×
              V13RealLinearRowsUnreadAssignment m
                (v13RealLinearSequentialPrefixTranscriptVectorRows pref)) =>
            z.1.val.val)
          h
    apply Prod.ext
    · exact hA
    · let rows := v13RealLinearSequentialPrefixTranscriptVectorRows pref
      let A := omega₀.val.val.1
      apply A.val.toEquiv.injective
      funext row
      by_cases hrow : row ∈ rows
      · let omega₀Prefix :
            V13RealLinearNoTargetSequentialPrefixWorldSet
              i₀ observer t pref :=
          ⟨omega₀.val.val, omega₀.property⟩
        let omega₁Prefix :
            V13RealLinearNoTargetSequentialPrefixWorldSet
              i₀ observer t pref :=
          ⟨omega₁.val.val, omega₁.property⟩
        have hview₀ :=
          v13RealLinearNoTargetSequentialPrefixWorldSet_rowView_eq
            omega₀Prefix ⟨row, hrow⟩
        have hview₁ :=
          v13RealLinearNoTargetSequentialPrefixWorldSet_rowView_eq
            omega₁Prefix ⟨row, hrow⟩
        have hbit₀ :
            A.val.toEquiv omega₀.val.val.2 row =
              (v13RealLinearSequentialPrefixTranscriptVectorRowView
                pref ⟨row, hrow⟩).2 := by
          simpa [A, omega₀Prefix, v13RealLinearRowView,
            v13RealLinearPublicInput] using (congrArg Prod.snd hview₀).symm
        have hbit₁ :
            A.val.toEquiv omega₁.val.val.2 row =
              (v13RealLinearSequentialPrefixTranscriptVectorRowView
                pref ⟨row, hrow⟩).2 := by
          simpa [A, omega₁Prefix, v13RealLinearRowView,
            v13RealLinearPublicInput, hA] using
            (congrArg Prod.snd hview₁).symm
        exact hbit₀.trans hbit₁.symm
      · have hassign :
            (fun unread : {row : Fin m // row ∉ rows} =>
                A.val.toEquiv omega₀.val.val.2 unread.1) =
              (fun unread : {row : Fin m // row ∉ rows} =>
                A.val.toEquiv omega₁.val.val.2 unread.1) := by
          simpa [rows, A, hA] using congrArg Prod.snd h
        exact congrFun hassign ⟨row, hrow⟩

theorem
    v13RealLinearNoTargetSequentialTraceFirstCosetHitOrderedPrefixWorldSet_card_le_hitMapClass_mul_unread
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (pref :
      V13RealLinearSequentialPrefixTranscriptVector m (t : Nat)) :
    Fintype.card
        (V13RealLinearNoTargetSequentialTraceFirstCosetHitOrderedPrefixWorldSet
          i₀ observer t pref) ≤
      Fintype.card
        (V13RealLinearNoTargetSequentialPrefixHitMapClass
          i₀ observer t pref
          (v13RealLinearSequentialPrefixTranscriptVectorNextRow observer
            pref)) *
        2 ^ (m -
          (v13RealLinearSequentialPrefixTranscriptVectorRows pref).card) := by
  classical
  let rows := v13RealLinearSequentialPrefixTranscriptVectorRows pref
  have hle :
      Fintype.card
          (V13RealLinearNoTargetSequentialTraceFirstCosetHitOrderedPrefixWorldSet
            i₀ observer t pref) ≤
        Fintype.card
          (V13RealLinearNoTargetSequentialPrefixHitMapClass
              i₀ observer t pref
              (v13RealLinearSequentialPrefixTranscriptVectorNextRow observer
                pref) ×
            V13RealLinearRowsUnreadAssignment m rows) :=
    Fintype.card_le_of_embedding
      (v13RealLinearNoTargetSequentialTraceFirstCosetHitOrderedPrefixWorldSetToHitMapClassTimesUnreadAssignment
        i₀ observer t pref)
  simpa [rows, Fintype.card_prod,
    v13RealLinearRowsUnreadAssignment_card] using hle

noncomputable def
    v13RealLinearNoTargetSequentialTraceFirstCosetHitOrderedPrefixWorldSetToFixedPrefixWorldSet
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (pref :
      V13RealLinearSequentialPrefixTranscriptVector m (t : Nat)) :
    V13RealLinearNoTargetSequentialTraceFirstCosetHitOrderedPrefixWorldSet
        i₀ observer t pref ↪
      V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixWorldSet
        i₀ observer t
        (v13RealLinearSequentialPrefixTranscriptVectorRows pref)
        (v13RealLinearSequentialPrefixTranscriptVectorNextRow observer
          pref) where
  toFun omega :=
    ⟨omega.val.val,
      ⟨omega.val.property,
        v13RealLinearNoTargetSequentialTraceFirstCosetHitOrderedPrefixWorldSet_prefixRows_eq
          i₀ observer t pref omega,
        v13RealLinearNoTargetSequentialTraceFirstCosetHitOrderedPrefixWorldSet_hitRow_eq
          i₀ observer t pref omega⟩⟩
  inj' := by
    intro omega₀ omega₁ h
    apply Subtype.ext
    apply Subtype.ext
    exact
      congrArg
        (fun omega :
          V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixWorldSet
            i₀ observer t
            (v13RealLinearSequentialPrefixTranscriptVectorRows pref)
            (v13RealLinearSequentialPrefixTranscriptVectorNextRow observer
              pref) => omega.val)
        h

theorem
    v13RealLinearNoTargetSequentialTraceFirstCosetHitOrderedPrefixWorldSet_card_le_fixedPrefix
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (pref :
      V13RealLinearSequentialPrefixTranscriptVector m (t : Nat)) :
    Fintype.card
        (V13RealLinearNoTargetSequentialTraceFirstCosetHitOrderedPrefixWorldSet
          i₀ observer t pref) ≤
      Fintype.card
        (V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixWorldSet
          i₀ observer t
          (v13RealLinearSequentialPrefixTranscriptVectorRows pref)
          (v13RealLinearSequentialPrefixTranscriptVectorNextRow observer
            pref)) :=
  Fintype.card_le_of_embedding
    (v13RealLinearNoTargetSequentialTraceFirstCosetHitOrderedPrefixWorldSetToFixedPrefixWorldSet
      i₀ observer t pref)

theorem
    v13RealLinearNoTargetSequentialTraceFirstCosetHitOrderedPrefixWorldSet_card_mul_two_pow_le_rows
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (pref :
      V13RealLinearSequentialPrefixTranscriptVector m (t : Nat)) :
    Fintype.card
        (V13RealLinearNoTargetSequentialTraceFirstCosetHitOrderedPrefixWorldSet
          i₀ observer t pref) *
      2 ^ m ≤
    4 * 2 ^ (v13RealLinearSequentialPrefixTranscriptVectorRows pref).card *
      Fintype.card
        (V13RealLinearAdaptiveQRowWorld m
          (V13RealLinearNoTargetRowsMap m i₀)) := by
  have hcard :
      Fintype.card
          (V13RealLinearNoTargetSequentialTraceFirstCosetHitOrderedPrefixWorldSet
            i₀ observer t pref) ≤
        Fintype.card
          (V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixWorldSet
            i₀ observer t
            (v13RealLinearSequentialPrefixTranscriptVectorRows pref)
            (v13RealLinearSequentialPrefixTranscriptVectorNextRow observer
              pref)) :=
    v13RealLinearNoTargetSequentialTraceFirstCosetHitOrderedPrefixWorldSet_card_le_fixedPrefix
      i₀ observer t pref
  have hfixed :=
    v13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixWorldSet_card_mul_two_pow_le_rows
      i₀ observer t
      (v13RealLinearSequentialPrefixTranscriptVectorRows pref)
      (v13RealLinearSequentialPrefixTranscriptVectorNextRow observer pref)
  exact (Nat.mul_le_mul_right (2 ^ m) hcard).trans hfixed

theorem
    v13RealLinearNoTargetSequentialTraceFirstCosetHitOrderedPrefixWorldSet_card_mul_two_pow_le_step
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (pref :
      V13RealLinearSequentialPrefixTranscriptVector m (t : Nat)) :
    Fintype.card
        (V13RealLinearNoTargetSequentialTraceFirstCosetHitOrderedPrefixWorldSet
          i₀ observer t pref) *
      2 ^ m ≤
    4 * 2 ^ (t : Nat) *
      Fintype.card
        (V13RealLinearAdaptiveQRowWorld m
          (V13RealLinearNoTargetRowsMap m i₀)) := by
  have hbase :=
    v13RealLinearNoTargetSequentialTraceFirstCosetHitOrderedPrefixWorldSet_card_mul_two_pow_le_rows
      i₀ observer t pref
  have hrows :
      (v13RealLinearSequentialPrefixTranscriptVectorRows pref).card ≤
        (t : Nat) :=
    v13RealLinearSequentialPrefixTranscriptVectorRows_card_le pref
  have hpow :
      2 ^ (v13RealLinearSequentialPrefixTranscriptVectorRows pref).card ≤
        2 ^ (t : Nat) :=
    Nat.pow_le_pow_right (by norm_num : 0 < 2) hrows
  have hmono :
      4 * 2 ^ (v13RealLinearSequentialPrefixTranscriptVectorRows pref).card *
          Fintype.card
            (V13RealLinearAdaptiveQRowWorld m
              (V13RealLinearNoTargetRowsMap m i₀)) ≤
        4 * 2 ^ (t : Nat) *
          Fintype.card
            (V13RealLinearAdaptiveQRowWorld m
              (V13RealLinearNoTargetRowsMap m i₀)) := by
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 4 hpow)
  exact hbase.trans hmono

noncomputable def
    v13RealLinearNoTargetSequentialTraceFirstCosetHitWorldSetEquivSigmaOrderedPrefix
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q) :
    V13RealLinearNoTargetSequentialTraceFirstCosetHitWorldSet
        i₀ observer t ≃
      (Σ pref :
          V13RealLinearSequentialPrefixTranscriptVector m (t : Nat),
        V13RealLinearNoTargetSequentialTraceFirstCosetHitOrderedPrefixWorldSet
          i₀ observer t pref) where
  toFun omega := by
    classical
    exact
      ⟨v13RealLinearSequentialPrefixTranscriptVectorOf observer
          (v13RealLinearPublicInput
            ({ x := omega.val.2, A := omega.val.1.val } :
              V13RealLinearWorld m))
          (t : Nat),
        ⟨omega, rfl⟩⟩
  invFun cell := by
    rcases cell with ⟨_prefix, cell⟩
    exact cell.val
  left_inv _omega := by
    rfl
  right_inv cell := by
    rcases cell with ⟨pref, cell⟩
    rcases cell with ⟨omega, hpref⟩
    cases hpref
    rfl

theorem
    v13RealLinearNoTargetSequentialTraceFirstCosetHitWorldSet_card_eq_sum_orderedPrefix
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q) :
    Fintype.card
        (V13RealLinearNoTargetSequentialTraceFirstCosetHitWorldSet
          i₀ observer t) =
      ∑ pref :
          V13RealLinearSequentialPrefixTranscriptVector m (t : Nat),
        Fintype.card
          (V13RealLinearNoTargetSequentialTraceFirstCosetHitOrderedPrefixWorldSet
            i₀ observer t pref) := by
  classical
  rw [Fintype.card_congr
    (v13RealLinearNoTargetSequentialTraceFirstCosetHitWorldSetEquivSigmaOrderedPrefix
      i₀ observer t)]
  rw [Fintype.card_sigma]

noncomputable def
    v13RealLinearNoTargetSequentialTraceFirstCosetHitWorldSetToFixedPrefixSigma
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q) :
    V13RealLinearNoTargetSequentialTraceFirstCosetHitWorldSet
        i₀ observer t ↪
      (Σ rows : Finset (Fin m),
        Σ row : Fin m,
          V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixWorldSet
            i₀ observer t rows row) where
  toFun omega := by
    classical
    let trace :=
      v13RealLinearNoTargetRowsSequentialQRowTrace i₀ observer omega.val
    exact
      ⟨v13RealLinearRowTracePrefixRows trace (t : Nat),
        ⟨trace.get ⟨(t : Nat), omega.property.1⟩,
          ⟨omega.val,
            ⟨omega.property, rfl,
              ⟨omega.property.1, rfl⟩⟩⟩⟩⟩
  inj' := by
    intro omega₀ omega₁ h
    apply Subtype.ext
    exact
      congrArg
        (fun z :
          (Σ rows : Finset (Fin m),
            Σ row : Fin m,
              V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixWorldSet
                i₀ observer t rows row) => z.2.2.val)
        h

theorem
    v13RealLinearNoTargetSequentialTraceFirstCosetHitWorldSet_card_le_sum_fixedPrefix
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q) :
    Fintype.card
        (V13RealLinearNoTargetSequentialTraceFirstCosetHitWorldSet
          i₀ observer t) ≤
      ∑ rows : Finset (Fin m),
        ∑ row : Fin m,
          Fintype.card
            (V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixWorldSet
              i₀ observer t rows row) := by
  classical
  have hle :
      Fintype.card
          (V13RealLinearNoTargetSequentialTraceFirstCosetHitWorldSet
            i₀ observer t) ≤
        Fintype.card
          (Σ rows : Finset (Fin m),
            Σ row : Fin m,
              V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixWorldSet
                i₀ observer t rows row) :=
    Fintype.card_le_of_embedding
      (v13RealLinearNoTargetSequentialTraceFirstCosetHitWorldSetToFixedPrefixSigma
        i₀ observer t)
  simpa [Fintype.card_sigma] using hle

theorem
    v13RealLinearNoTargetSequentialTraceFirstCosetHitOrderedPrefixWorldSet_sum_card_le_sum_fixedPrefix
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q) :
    (∑ pref :
        V13RealLinearSequentialPrefixTranscriptVector m (t : Nat),
      Fintype.card
        (V13RealLinearNoTargetSequentialTraceFirstCosetHitOrderedPrefixWorldSet
          i₀ observer t pref)) ≤
      ∑ rows : Finset (Fin m),
        ∑ row : Fin m,
          Fintype.card
            (V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixWorldSet
              i₀ observer t rows row) := by
  rw [←
    v13RealLinearNoTargetSequentialTraceFirstCosetHitWorldSet_card_eq_sum_orderedPrefix
      i₀ observer t]
  exact
    v13RealLinearNoTargetSequentialTraceFirstCosetHitWorldSet_card_le_sum_fixedPrefix
      i₀ observer t

/-- The exact remaining adaptive summation surface for Step 0: after splitting
one step's trace-coset hit event by the realized prefix rowset and next row,
the total fixed-prefix fiber mass must fit the same per-step bound. -/
def
    V13RealLinearNoTargetRowsSequentialTraceCosetHitFixedPrefixPackingBound
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) : Prop :=
  ∀ t : Fin q,
    (∑ rows : Finset (Fin m),
      ∑ row : Fin m,
        Fintype.card
          (V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixWorldSet
            i₀ observer t rows row)) *
      2 ^ m ≤
    (4 * 2 ^ (t : Nat)) *
      Fintype.card
        (V13RealLinearAdaptiveQRowWorld m
          (V13RealLinearNoTargetRowsMap m i₀))

/-- Transcript-cylinder refinement of the fixed-prefix packing surface.  This
is equivalent to fixed-prefix packing, but exposes the row-transcript cells
where the remaining no-target adaptive packing argument should act. -/
def
    V13RealLinearNoTargetRowsSequentialTraceCosetHitFixedPrefixTranscriptPackingBound
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) : Prop :=
  ∀ t : Fin q,
    (∑ rows : Finset (Fin m),
      ∑ row : Fin m,
        ∑ transcript : V13RealLinearRowsTranscriptSpace m rows,
          Fintype.card
            (V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixTranscriptWorldSet
              i₀ observer t rows row transcript)) *
      2 ^ m ≤
    (4 * 2 ^ (t : Nat)) *
      Fintype.card
        (V13RealLinearAdaptiveQRowWorld m
          (V13RealLinearNoTargetRowsMap m i₀))

/-- Active fixed-map transcript-cylinder capacity form of the remaining
Step 0 packing surface.  The fixed-prefix transcript sigma has already been
identified with this active capacity sum; the remaining work is the genuine
conditioned-basis counting bound.

Current live pin: generated-prefix cells have exact hidden-vector completion
count, and the active generated-prefix cells containing any fixed full world
are bounded by the `2 ^ ((t : Nat) + 1)` ordered RHS histories.  The remaining
overcharge is the normalized summation needed by this capacity statement:
after a generated-prefix cell completion is projected to its full world
`(A, x)`, the extra `2 ^ m` normalizer in the division-free count is forgotten.
Thus a fixed world and transcript history can be charged once as an active
cell, while the proof still needs to distinguish the additional normalizer
completions and route them through the no-target map-conditioning count.  A
closure must carry that unread-assignment/normalizer data into an injective
no-target map charge, or prove an equivalent normalized generated-cell
summation before applying the factor-2 generated-rowset capacity reduction. -/
def
    V13RealLinearNoTargetRowsSequentialTraceCosetHitActiveFixedMapTranscriptCylinderCapacityBound
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) : Prop :=
  ∀ t : Fin q,
    (∑ activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t,
      2 ^ (m - activeIdx.1.rows.card)) *
      2 ^ m ≤
    (4 * 2 ^ (t : Nat)) *
      Fintype.card
        (V13RealLinearAdaptiveQRowWorld m
          (V13RealLinearNoTargetRowsMap m i₀))

/-- Ordered-prefix packing surface for Step 0.  This partitions the first-hit
event by the exact ordered transcript prefix used by the sequential observer,
so the remaining capacity argument can work on deterministic next-row
cylinders rather than unordered rowsets. -/
def
    V13RealLinearNoTargetRowsSequentialTraceCosetHitOrderedPrefixPackingBound
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) : Prop :=
  ∀ t : Fin q,
    (∑ pref :
        V13RealLinearSequentialPrefixTranscriptVector m (t : Nat),
      Fintype.card
        (V13RealLinearNoTargetSequentialTraceFirstCosetHitOrderedPrefixWorldSet
          i₀ observer t pref)) *
      2 ^ m ≤
    (4 * 2 ^ (t : Nat)) *
      Fintype.card
        (V13RealLinearAdaptiveQRowWorld m
          (V13RealLinearNoTargetRowsMap m i₀))

/-- Conditioned ordered-prefix counting pin for Step 0.  Once a prefix
transcript is fixed, the hit fiber must have normalized mass at most
`4 * 2^k / 2^m`, where `k` is the number of distinct rows in that prefix.  The
ambient class on the right is the full set of no-target worlds realizing the
same ordered prefix. -/
def
    V13RealLinearNoTargetRowsSequentialTraceCosetHitOrderedPrefixConditionedCountingBound
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) : Prop :=
  ∀ t : Fin q,
    ∀ pref :
      V13RealLinearSequentialPrefixTranscriptVector m (t : Nat),
      Fintype.card
          (V13RealLinearNoTargetSequentialTraceFirstCosetHitOrderedPrefixWorldSet
            i₀ observer t pref) *
        2 ^ m ≤
      (4 *
          2 ^ (v13RealLinearSequentialPrefixTranscriptVectorRows pref).card) *
        Fintype.card
          (V13RealLinearNoTargetSequentialPrefixWorldSet
            i₀ observer t pref)

theorem
    V13RealLinearNoTargetRowsSequentialTraceCosetHitOrderedPrefixConditionedCountingBound_of_freshnessBridge
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q)
    (hfreshBridge :
      V13RealLinearNoTargetRowsSequentialTraceCosetHitOrderedPrefixFreshnessBridge
        i₀ observer) :
    V13RealLinearNoTargetRowsSequentialTraceCosetHitOrderedPrefixConditionedCountingBound
      i₀ observer := by
  classical
  intro t pref
  let rows := v13RealLinearSequentialPrefixTranscriptVectorRows pref
  let row₁ := v13RealLinearSequentialPrefixTranscriptVectorNextRow observer pref
  let HitW :=
    V13RealLinearNoTargetSequentialTraceFirstCosetHitOrderedPrefixWorldSet
      i₀ observer t pref
  let HitM :=
    V13RealLinearNoTargetSequentialPrefixHitMapClass
      i₀ observer t pref row₁
  let PrefM :=
    V13RealLinearNoTargetSequentialPrefixMapClass
      i₀ observer t pref
  let PrefW :=
    V13RealLinearNoTargetSequentialPrefixWorldSet
      i₀ observer t pref
  let Ucard := 2 ^ (m - rows.card)
  let M := 2 ^ m
  let K := 2 ^ rows.card
  by_cases hfresh : row₁ ∉ rows
  · have hHitW :
        Fintype.card HitW ≤ Fintype.card HitM * Ucard := by
      simpa [HitW, HitM, rows, row₁, Ucard] using
        v13RealLinearNoTargetSequentialTraceFirstCosetHitOrderedPrefixWorldSet_card_le_hitMapClass_mul_unread
          i₀ observer t pref
    have hPrefW :
        Fintype.card PrefM * Ucard ≤ Fintype.card PrefW := by
      simpa [PrefM, PrefW, rows, Ucard] using
        v13RealLinearNoTargetSequentialPrefixMapClass_card_mul_unread_le_prefixWorldSet
          i₀ observer t pref
    have hHitM :
        Fintype.card HitM * M ≤ 4 * K * Fintype.card PrefM := by
      simpa [HitM, PrefM, rows, row₁, M, K] using
        v13RealLinearNoTargetSequentialPrefixHitMapClass_card_mul_two_pow_le_prefixMapClass
          i₀ observer t pref hfresh
    calc
      Fintype.card HitW * M ≤
          (Fintype.card HitM * Ucard) * M := by
            exact Nat.mul_le_mul_right M hHitW
      _ = (Fintype.card HitM * M) * Ucard := by ring
      _ ≤ (4 * K * Fintype.card PrefM) * Ucard := by
            exact Nat.mul_le_mul_right Ucard hHitM
      _ = (4 * K) * (Fintype.card PrefM * Ucard) := by ring
      _ ≤ (4 * K) * Fintype.card PrefW := by
            exact Nat.mul_le_mul_left (4 * K) hPrefW
      _ =
          (4 *
              2 ^ (v13RealLinearSequentialPrefixTranscriptVectorRows pref).card) *
            Fintype.card
              (V13RealLinearNoTargetSequentialPrefixWorldSet
                i₀ observer t pref) := by
            simp [PrefW, rows, K]
  · have hzero : Fintype.card HitW = 0 := by
      rw [Fintype.card_eq_zero_iff]
      refine ⟨?_⟩
      intro omega
      exact hfresh (hfreshBridge t pref omega)
    simp [HitW, hzero]

theorem
    V13RealLinearNoTargetRowsSequentialTraceCosetHitOrderedPrefixConditionedCountingBound_of_noPriorBridge
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q)
    (hprior :
      V13RealLinearNoTargetRowsSequentialTraceCosetHitNoPriorBridge
        i₀ observer) :
    V13RealLinearNoTargetRowsSequentialTraceCosetHitOrderedPrefixConditionedCountingBound
      i₀ observer :=
  V13RealLinearNoTargetRowsSequentialTraceCosetHitOrderedPrefixConditionedCountingBound_of_freshnessBridge
    i₀ observer
    (V13RealLinearNoTargetRowsSequentialTraceCosetHitOrderedPrefixFreshnessBridge_of_noPrior
      i₀ observer hprior)

theorem
    V13RealLinearNoTargetRowsSequentialTraceCosetHitOrderedPrefixPackingBound_of_conditionedCounting
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q)
    (hconditioned :
      V13RealLinearNoTargetRowsSequentialTraceCosetHitOrderedPrefixConditionedCountingBound
        i₀ observer) :
    V13RealLinearNoTargetRowsSequentialTraceCosetHitOrderedPrefixPackingBound
      i₀ observer := by
  classical
  intro t
  let Hit := fun pref :
      V13RealLinearSequentialPrefixTranscriptVector m (t : Nat) =>
    Fintype.card
      (V13RealLinearNoTargetSequentialTraceFirstCosetHitOrderedPrefixWorldSet
        i₀ observer t pref)
  let Class := fun pref :
      V13RealLinearSequentialPrefixTranscriptVector m (t : Nat) =>
    Fintype.card
      (V13RealLinearNoTargetSequentialPrefixWorldSet
        i₀ observer t pref)
  let Q := 4 * 2 ^ (t : Nat)
  have hconditionedSum :
      (∑ pref :
          V13RealLinearSequentialPrefixTranscriptVector m (t : Nat),
        Hit pref) *
        2 ^ m ≤
      ∑ pref :
          V13RealLinearSequentialPrefixTranscriptVector m (t : Nat),
        (4 *
            2 ^ (v13RealLinearSequentialPrefixTranscriptVectorRows pref).card) *
          Class pref := by
    calc
      (∑ pref :
          V13RealLinearSequentialPrefixTranscriptVector m (t : Nat),
        Hit pref) *
        2 ^ m =
          ∑ pref :
              V13RealLinearSequentialPrefixTranscriptVector m (t : Nat),
            Hit pref * 2 ^ m := by
            rw [Finset.sum_mul]
      _ ≤
          ∑ pref :
              V13RealLinearSequentialPrefixTranscriptVector m (t : Nat),
            (4 *
                2 ^ (v13RealLinearSequentialPrefixTranscriptVectorRows pref).card) *
              Class pref := by
            apply Finset.sum_le_sum
            intro pref _hpref
            simpa [Hit, Class] using hconditioned t pref
  have htoStep :
      (∑ pref :
          V13RealLinearSequentialPrefixTranscriptVector m (t : Nat),
        (4 *
            2 ^ (v13RealLinearSequentialPrefixTranscriptVectorRows pref).card) *
          Class pref) ≤
      ∑ pref :
          V13RealLinearSequentialPrefixTranscriptVector m (t : Nat),
        Q * Class pref := by
    apply Finset.sum_le_sum
    intro pref _hpref
    have hrows :
        (v13RealLinearSequentialPrefixTranscriptVectorRows pref).card ≤
          (t : Nat) :=
      v13RealLinearSequentialPrefixTranscriptVectorRows_card_le pref
    have hpow :
        2 ^ (v13RealLinearSequentialPrefixTranscriptVectorRows pref).card ≤
          2 ^ (t : Nat) :=
      Nat.pow_le_pow_right (by norm_num : 0 < 2) hrows
    have hcoef :
        4 *
            2 ^ (v13RealLinearSequentialPrefixTranscriptVectorRows pref).card ≤
          Q := by
      exact Nat.mul_le_mul_left 4 hpow
    exact Nat.mul_le_mul_right (Class pref) hcoef
  have hclassSum :
      (∑ pref :
          V13RealLinearSequentialPrefixTranscriptVector m (t : Nat),
        Q * Class pref) =
      Q *
        Fintype.card
          (V13RealLinearAdaptiveQRowWorld m
            (V13RealLinearNoTargetRowsMap m i₀)) := by
    calc
      (∑ pref :
          V13RealLinearSequentialPrefixTranscriptVector m (t : Nat),
        Q * Class pref) =
          Q *
            ∑ pref :
                V13RealLinearSequentialPrefixTranscriptVector m (t : Nat),
              Class pref := by
            rw [← Finset.mul_sum]
      _ =
          Q *
            Fintype.card
              (V13RealLinearAdaptiveQRowWorld m
                (V13RealLinearNoTargetRowsMap m i₀)) := by
            rw [
              v13RealLinearNoTargetSequentialPrefixWorldSet_sum_card_eq_world
                i₀ observer t]
  exact
    (hconditionedSum.trans htoStep).trans_eq
      (by
        simpa [Hit, Class, Q,
          V13RealLinearNoTargetRowsSequentialTraceCosetHitOrderedPrefixPackingBound]
          using hclassSum)

theorem
    V13RealLinearNoTargetRowsSequentialTraceCosetHitFixedPrefixPackingBound_of_transcriptPacking
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q)
    (hpack :
      V13RealLinearNoTargetRowsSequentialTraceCosetHitFixedPrefixTranscriptPackingBound
        i₀ observer) :
    V13RealLinearNoTargetRowsSequentialTraceCosetHitFixedPrefixPackingBound
      i₀ observer := by
  classical
  intro t
  have hsum :
      (∑ rows : Finset (Fin m),
        ∑ row : Fin m,
          Fintype.card
            (V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixWorldSet
              i₀ observer t rows row)) =
        ∑ rows : Finset (Fin m),
          ∑ row : Fin m,
            ∑ transcript : V13RealLinearRowsTranscriptSpace m rows,
              Fintype.card
                (V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixTranscriptWorldSet
                  i₀ observer t rows row transcript) := by
    apply Finset.sum_congr rfl
    intro rows _hrows
    apply Finset.sum_congr rfl
    intro row _hrow
    exact
      v13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixWorldSet_card_eq_sum_transcripts
        i₀ observer t rows row
  simpa [V13RealLinearNoTargetRowsSequentialTraceCosetHitFixedPrefixPackingBound,
    V13RealLinearNoTargetRowsSequentialTraceCosetHitFixedPrefixTranscriptPackingBound,
    hsum] using hpack t

theorem
    V13RealLinearNoTargetRowsSequentialTraceCosetHitFixedPrefixTranscriptPackingBound_of_activeFixedMapTranscriptCylinderCapacity
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q)
    (hcapacity :
      V13RealLinearNoTargetRowsSequentialTraceCosetHitActiveFixedMapTranscriptCylinderCapacityBound
        i₀ observer) :
    V13RealLinearNoTargetRowsSequentialTraceCosetHitFixedPrefixTranscriptPackingBound
      i₀ observer := by
  classical
  intro t
  rw [
    v13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixTranscriptWorldSet_sum_card_eq_active_capacity
      i₀ observer t]
  exact hcapacity t

theorem
    V13RealLinearNoTargetRowsSequentialTraceCosetHitActiveFixedMapTranscriptCylinderCapacityBound_of_fixedPrefixTranscriptPacking
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q)
    (hpack :
      V13RealLinearNoTargetRowsSequentialTraceCosetHitFixedPrefixTranscriptPackingBound
        i₀ observer) :
    V13RealLinearNoTargetRowsSequentialTraceCosetHitActiveFixedMapTranscriptCylinderCapacityBound
      i₀ observer := by
  classical
  intro t
  have hstep := hpack t
  rw [
    v13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixTranscriptWorldSet_sum_card_eq_active_capacity
      i₀ observer t] at hstep
  exact hstep

theorem
    V13RealLinearNoTargetRowsSequentialTraceCosetHitActiveFixedMapTranscriptCylinderCapacityBound_iff_fixedPrefixTranscriptPacking
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) :
    V13RealLinearNoTargetRowsSequentialTraceCosetHitActiveFixedMapTranscriptCylinderCapacityBound
      i₀ observer ↔
    V13RealLinearNoTargetRowsSequentialTraceCosetHitFixedPrefixTranscriptPackingBound
      i₀ observer :=
  ⟨V13RealLinearNoTargetRowsSequentialTraceCosetHitFixedPrefixTranscriptPackingBound_of_activeFixedMapTranscriptCylinderCapacity
      i₀ observer,
    V13RealLinearNoTargetRowsSequentialTraceCosetHitActiveFixedMapTranscriptCylinderCapacityBound_of_fixedPrefixTranscriptPacking
      i₀ observer⟩

theorem
    V13RealLinearNoTargetRowsSequentialTraceCosetHitOrderedPrefixPackingBound_of_fixedPrefixPacking
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q)
    (hpack :
      V13RealLinearNoTargetRowsSequentialTraceCosetHitFixedPrefixPackingBound
        i₀ observer) :
    V13RealLinearNoTargetRowsSequentialTraceCosetHitOrderedPrefixPackingBound
      i₀ observer := by
  classical
  intro t
  let orderedSum :=
    ∑ pref :
      V13RealLinearSequentialPrefixTranscriptVector m (t : Nat),
      Fintype.card
        (V13RealLinearNoTargetSequentialTraceFirstCosetHitOrderedPrefixWorldSet
          i₀ observer t pref)
  let fixedSum :=
    ∑ rows : Finset (Fin m),
      ∑ row : Fin m,
        Fintype.card
          (V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixWorldSet
            i₀ observer t rows row)
  have hle : orderedSum ≤ fixedSum := by
    simpa [orderedSum, fixedSum] using
      v13RealLinearNoTargetSequentialTraceFirstCosetHitOrderedPrefixWorldSet_sum_card_le_sum_fixedPrefix
        i₀ observer t
  have hmul : orderedSum * 2 ^ m ≤ fixedSum * 2 ^ m :=
    Nat.mul_le_mul_right (2 ^ m) hle
  have hfixed :
      fixedSum * 2 ^ m ≤
        (4 * 2 ^ (t : Nat)) *
          Fintype.card
            (V13RealLinearAdaptiveQRowWorld m
              (V13RealLinearNoTargetRowsMap m i₀)) := by
    simpa [fixedSum,
      V13RealLinearNoTargetRowsSequentialTraceCosetHitFixedPrefixPackingBound]
      using hpack t
  exact hmul.trans hfixed

theorem
    V13RealLinearNoTargetRowsSequentialTraceCosetHitFixedPrefixTranscriptPackingBound_of_fixedPrefixPacking
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q)
    (hpack :
      V13RealLinearNoTargetRowsSequentialTraceCosetHitFixedPrefixPackingBound
        i₀ observer) :
    V13RealLinearNoTargetRowsSequentialTraceCosetHitFixedPrefixTranscriptPackingBound
      i₀ observer := by
  classical
  intro t
  have hsum :
      (∑ rows : Finset (Fin m),
        ∑ row : Fin m,
          Fintype.card
            (V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixWorldSet
              i₀ observer t rows row)) =
        ∑ rows : Finset (Fin m),
          ∑ row : Fin m,
            ∑ transcript : V13RealLinearRowsTranscriptSpace m rows,
              Fintype.card
                (V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixTranscriptWorldSet
                  i₀ observer t rows row transcript) := by
    apply Finset.sum_congr rfl
    intro rows _hrows
    apply Finset.sum_congr rfl
    intro row _hrow
    exact
      v13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixWorldSet_card_eq_sum_transcripts
        i₀ observer t rows row
  simpa [V13RealLinearNoTargetRowsSequentialTraceCosetHitFixedPrefixPackingBound,
    V13RealLinearNoTargetRowsSequentialTraceCosetHitFixedPrefixTranscriptPackingBound,
    hsum] using hpack t

theorem
    V13RealLinearNoTargetRowsSequentialTraceCosetHitFixedPrefixPackingBound_iff_transcriptPacking
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) :
    V13RealLinearNoTargetRowsSequentialTraceCosetHitFixedPrefixPackingBound
      i₀ observer ↔
    V13RealLinearNoTargetRowsSequentialTraceCosetHitFixedPrefixTranscriptPackingBound
      i₀ observer :=
  ⟨V13RealLinearNoTargetRowsSequentialTraceCosetHitFixedPrefixTranscriptPackingBound_of_fixedPrefixPacking
      i₀ observer,
    V13RealLinearNoTargetRowsSequentialTraceCosetHitFixedPrefixPackingBound_of_transcriptPacking
      i₀ observer⟩

theorem
    V13RealLinearNoTargetRowsSequentialTraceCosetHitCountingBound_of_fixedPrefixPacking
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q)
    (hpack :
      V13RealLinearNoTargetRowsSequentialTraceCosetHitFixedPrefixPackingBound
        i₀ observer) :
    V13RealLinearNoTargetRowsSequentialTraceCosetHitCountingBound
      i₀ observer := by
  classical
  unfold V13RealLinearNoTargetRowsSequentialTraceCosetHitCountingBound
  unfold V13RealLinearAdaptiveQRowTraceCosetHitCountingBound
  unfold V13RealLinearAdaptiveDeferredDecisionNewCaptureCountingBound
  intro t
  let Full :=
    V13RealLinearNoTargetSequentialTraceFirstCosetHitWorldSet
      i₀ observer t
  let FiberSum :=
    ∑ rows : Finset (Fin m),
      ∑ row : Fin m,
        Fintype.card
          (V13RealLinearNoTargetSequentialTraceFirstCosetHitFixedPrefixWorldSet
            i₀ observer t rows row)
  have hfullLe : Fintype.card Full ≤ FiberSum := by
    simpa [Full, FiberSum] using
      v13RealLinearNoTargetSequentialTraceFirstCosetHitWorldSet_card_le_sum_fixedPrefix
        i₀ observer t
  have hmul :
      Fintype.card Full * 2 ^ m ≤ FiberSum * 2 ^ m :=
    Nat.mul_le_mul_right (2 ^ m) hfullLe
  have hpackStep :
      FiberSum * 2 ^ m ≤
        (4 * 2 ^ (t : Nat)) *
          Fintype.card
            (V13RealLinearAdaptiveQRowWorld m
              (V13RealLinearNoTargetRowsMap m i₀)) := by
    simpa [V13RealLinearNoTargetRowsSequentialTraceCosetHitFixedPrefixPackingBound,
      FiberSum] using hpack t
  exact hmul.trans hpackStep

theorem
    V13RealLinearNoTargetRowsSequentialTraceCosetHitCountingBound_of_fixedPrefixTranscriptPacking
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q)
    (hpack :
      V13RealLinearNoTargetRowsSequentialTraceCosetHitFixedPrefixTranscriptPackingBound
        i₀ observer) :
    V13RealLinearNoTargetRowsSequentialTraceCosetHitCountingBound
      i₀ observer :=
  V13RealLinearNoTargetRowsSequentialTraceCosetHitCountingBound_of_fixedPrefixPacking
    i₀ observer
    (V13RealLinearNoTargetRowsSequentialTraceCosetHitFixedPrefixPackingBound_of_transcriptPacking
      i₀ observer hpack)

theorem
    V13RealLinearNoTargetRowsSequentialTraceCosetHitCountingBound_of_activeFixedMapTranscriptCylinderCapacity
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q)
    (hcapacity :
      V13RealLinearNoTargetRowsSequentialTraceCosetHitActiveFixedMapTranscriptCylinderCapacityBound
        i₀ observer) :
    V13RealLinearNoTargetRowsSequentialTraceCosetHitCountingBound
      i₀ observer :=
  V13RealLinearNoTargetRowsSequentialTraceCosetHitCountingBound_of_fixedPrefixTranscriptPacking
    i₀ observer
    (V13RealLinearNoTargetRowsSequentialTraceCosetHitFixedPrefixTranscriptPackingBound_of_activeFixedMapTranscriptCylinderCapacity
      i₀ observer hcapacity)

theorem
    V13RealLinearNoTargetRowsSequentialTraceCosetHitActiveFixedMapTranscriptCylinderCapacityBound_of_counting
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q)
    (hcount :
      V13RealLinearNoTargetRowsSequentialTraceCosetHitCountingBound
        i₀ observer) :
    V13RealLinearNoTargetRowsSequentialTraceCosetHitActiveFixedMapTranscriptCylinderCapacityBound
      i₀ observer := by
  classical
  intro t
  unfold V13RealLinearNoTargetRowsSequentialTraceCosetHitCountingBound at hcount
  unfold V13RealLinearAdaptiveQRowTraceCosetHitCountingBound at hcount
  unfold V13RealLinearAdaptiveDeferredDecisionNewCaptureCountingBound at hcount
  have hstep := hcount t
  change
    Fintype.card
        (V13RealLinearNoTargetSequentialTraceFirstCosetHitWorldSet
          i₀ observer t) *
      2 ^ m ≤
    (4 * 2 ^ (t : Nat)) *
      Fintype.card
        (V13RealLinearAdaptiveQRowWorld m
          (V13RealLinearNoTargetRowsMap m i₀)) at hstep
  rw [
    v13RealLinearNoTargetSequentialTraceFirstCosetHitWorldSet_card_eq_active_capacity
      i₀ observer t] at hstep
  exact hstep

theorem
    V13RealLinearNoTargetRowsSequentialTraceCosetHitActiveFixedMapTranscriptCylinderCapacityBound_iff_counting
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) :
    V13RealLinearNoTargetRowsSequentialTraceCosetHitActiveFixedMapTranscriptCylinderCapacityBound
      i₀ observer ↔
    V13RealLinearNoTargetRowsSequentialTraceCosetHitCountingBound
      i₀ observer :=
  ⟨V13RealLinearNoTargetRowsSequentialTraceCosetHitCountingBound_of_activeFixedMapTranscriptCylinderCapacity
      i₀ observer,
    V13RealLinearNoTargetRowsSequentialTraceCosetHitActiveFixedMapTranscriptCylinderCapacityBound_of_counting
      i₀ observer⟩

theorem
    v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_sum_eq_zero_of_zero_index
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (ht : (t : Nat) = 0) :
    (∑ activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t,
      2 ^ (m - activeIdx.1.rows.card)) = 0 := by
  classical
  rw [←
    v13RealLinearNoTargetSequentialTraceFirstCosetHitWorldSet_card_eq_active_capacity
      i₀ observer t]
  exact
    v13RealLinearNoTargetRowsSequentialTraceFirstCosetHit_card_eq_zero_of_zero_index
      i₀ observer t ht

theorem
    v13RealLinearNoTargetRowsSequentialTraceCosetHitActiveFixedMapTranscriptCylinderCapacityBound_zeroIndex
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) (t : Fin q)
    (ht : (t : Nat) = 0) :
    (∑ activeIdx :
      V13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinderIndex
        i₀ observer t,
      2 ^ (m - activeIdx.1.rows.card)) *
      2 ^ m ≤
    (4 * 2 ^ (t : Nat)) *
      Fintype.card
        (V13RealLinearAdaptiveQRowWorld m
          (V13RealLinearNoTargetRowsMap m i₀)) := by
  rw [
    v13RealLinearNoTargetSequentialTraceFirstCosetHitActiveFixedMapTranscriptCylinder_sum_eq_zero_of_zero_index
      i₀ observer t ht]
  simp

theorem
    V13RealLinearNoTargetRowsSequentialTraceCosetHitActiveFixedMapTranscriptCylinderCapacityBound_oneBudget
    {m : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m 1) :
    V13RealLinearNoTargetRowsSequentialTraceCosetHitActiveFixedMapTranscriptCylinderCapacityBound
      i₀ observer := by
  intro t
  have ht : (t : Nat) = 0 := by
    omega
  exact
    v13RealLinearNoTargetRowsSequentialTraceCosetHitActiveFixedMapTranscriptCylinderCapacityBound_zeroIndex
      i₀ observer t ht

theorem
    V13RealLinearNoTargetRowsSequentialTraceCosetHitCountingBound_of_orderedPrefixPacking
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q)
    (hpack :
      V13RealLinearNoTargetRowsSequentialTraceCosetHitOrderedPrefixPackingBound
        i₀ observer) :
    V13RealLinearNoTargetRowsSequentialTraceCosetHitCountingBound
      i₀ observer := by
  classical
  unfold V13RealLinearNoTargetRowsSequentialTraceCosetHitCountingBound
  unfold V13RealLinearAdaptiveQRowTraceCosetHitCountingBound
  unfold V13RealLinearAdaptiveDeferredDecisionNewCaptureCountingBound
  intro t
  change
    Fintype.card
        (V13RealLinearNoTargetSequentialTraceFirstCosetHitWorldSet
          i₀ observer t) *
      2 ^ m ≤
    (4 * 2 ^ (t : Nat)) *
      Fintype.card
        (V13RealLinearAdaptiveQRowWorld m
          (V13RealLinearNoTargetRowsMap m i₀))
  rw [
    v13RealLinearNoTargetSequentialTraceFirstCosetHitWorldSet_card_eq_sum_orderedPrefix
      i₀ observer t]
  simpa
    [V13RealLinearNoTargetRowsSequentialTraceCosetHitOrderedPrefixPackingBound]
    using hpack t

theorem
    V13RealLinearNoTargetRowsSequentialTraceCosetHitOrderedPrefixPackingBound_of_counting
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q)
    (hcount :
      V13RealLinearNoTargetRowsSequentialTraceCosetHitCountingBound
        i₀ observer) :
    V13RealLinearNoTargetRowsSequentialTraceCosetHitOrderedPrefixPackingBound
      i₀ observer := by
  classical
  intro t
  unfold V13RealLinearNoTargetRowsSequentialTraceCosetHitCountingBound at hcount
  unfold V13RealLinearAdaptiveQRowTraceCosetHitCountingBound at hcount
  unfold V13RealLinearAdaptiveDeferredDecisionNewCaptureCountingBound at hcount
  have hstep := hcount t
  change
    Fintype.card
        (V13RealLinearNoTargetSequentialTraceFirstCosetHitWorldSet
          i₀ observer t) *
      2 ^ m ≤
    (4 * 2 ^ (t : Nat)) *
      Fintype.card
        (V13RealLinearAdaptiveQRowWorld m
          (V13RealLinearNoTargetRowsMap m i₀)) at hstep
  rw [
    v13RealLinearNoTargetSequentialTraceFirstCosetHitWorldSet_card_eq_sum_orderedPrefix
      i₀ observer t] at hstep
  simpa
    [V13RealLinearNoTargetRowsSequentialTraceCosetHitOrderedPrefixPackingBound]
    using hstep

theorem
    V13RealLinearNoTargetRowsSequentialTraceCosetHitOrderedPrefixPackingBound_iff_counting
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q) :
    V13RealLinearNoTargetRowsSequentialTraceCosetHitOrderedPrefixPackingBound
      i₀ observer ↔
    V13RealLinearNoTargetRowsSequentialTraceCosetHitCountingBound
      i₀ observer :=
  ⟨V13RealLinearNoTargetRowsSequentialTraceCosetHitCountingBound_of_orderedPrefixPacking
      i₀ observer,
    V13RealLinearNoTargetRowsSequentialTraceCosetHitOrderedPrefixPackingBound_of_counting
      i₀ observer⟩

theorem
    V13RealLinearNoTargetRowsSequentialTraceCosetHitCountingBound_of_orderedPrefixConditionedCounting
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q)
    (hconditioned :
      V13RealLinearNoTargetRowsSequentialTraceCosetHitOrderedPrefixConditionedCountingBound
        i₀ observer) :
    V13RealLinearNoTargetRowsSequentialTraceCosetHitCountingBound
      i₀ observer :=
  V13RealLinearNoTargetRowsSequentialTraceCosetHitCountingBound_of_orderedPrefixPacking
    i₀ observer
    (V13RealLinearNoTargetRowsSequentialTraceCosetHitOrderedPrefixPackingBound_of_conditionedCounting
      i₀ observer hconditioned)

theorem
    V13RealLinearNoTargetRowsSequentialTraceCosetHitActiveFixedMapTranscriptCylinderCapacityBound_of_orderedPrefixConditionedCounting
    {m q : Nat} (i₀ : Fin m)
    (observer : V13RealLinearSequentialRowObserver m q)
    (hconditioned :
      V13RealLinearNoTargetRowsSequentialTraceCosetHitOrderedPrefixConditionedCountingBound
        i₀ observer) :
    V13RealLinearNoTargetRowsSequentialTraceCosetHitActiveFixedMapTranscriptCylinderCapacityBound
      i₀ observer :=
  V13RealLinearNoTargetRowsSequentialTraceCosetHitActiveFixedMapTranscriptCylinderCapacityBound_of_counting
    i₀ observer
    (V13RealLinearNoTargetRowsSequentialTraceCosetHitCountingBound_of_orderedPrefixConditionedCounting
      i₀ observer hconditioned)

abbrev V13RealLinearNoTargetFixedPairCosetHitMapSet {m : Nat}
    (i₀ row₀ row₁ : Fin m) :=
  {A : V13RealLinearNoTargetRowsMap m i₀ //
    V13RealLinearRowFunctionalTargetCosetHit A.val
      ({row₀} : Finset (Fin m)) i₀ row₁}

noncomputable instance {m : Nat} (i₀ row₀ row₁ : Fin m) :
    Fintype (V13RealLinearNoTargetFixedPairCosetHitMapSet
      i₀ row₀ row₁) := by
  classical
  unfold V13RealLinearNoTargetFixedPairCosetHitMapSet
  infer_instance

noncomputable def
    v13RealLinearNoTargetFixedPairCosetHitMapSetEmbeddingFunctionalTableHit
    {m : Nat} (i₀ row₀ row₁ : Fin m) :
    V13RealLinearNoTargetFixedPairCosetHitMapSet i₀ row₀ row₁ ↪
      {table : V13RealLinearRowFunctionalTable m //
        V13RealLinearFunctionalTableTargetCosetHit table
          ({row₀} : Finset (Fin m)) i₀ row₁} where
  toFun A :=
    ⟨v13RealLinearRowFunctionalTableOfEquiv A.val.val,
      v13RealLinearFunctionalTableTargetCosetHit_of_rowFunctionalTargetCosetHit
        A.property⟩
  inj' := by
    intro A₀ A₁ h
    apply Subtype.ext
    apply Subtype.ext
    apply v13RealLinearRowFunctionalTableOfEquiv_injective
    exact congrArg Subtype.val h

theorem
    v13RealLinearNoTargetFixedPairCosetHitMapSet_card_mul_two_pow_le_table
    {m : Nat} (i₀ row₀ row₁ : Fin m)
    (hrow : row₁ ∉ ({row₀} : Finset (Fin m))) :
    Fintype.card
        (V13RealLinearNoTargetFixedPairCosetHitMapSet i₀ row₀ row₁) *
      2 ^ m ≤
    2 * Fintype.card (V13RealLinearRowFunctionalTable m) := by
  classical
  let S := V13RealLinearNoTargetFixedPairCosetHitMapSet i₀ row₀ row₁
  let H :=
    {table : V13RealLinearRowFunctionalTable m //
      V13RealLinearFunctionalTableTargetCosetHit table
        ({row₀} : Finset (Fin m)) i₀ row₁}
  have hSle : Fintype.card S ≤ Fintype.card H :=
    Fintype.card_le_of_embedding
      (v13RealLinearNoTargetFixedPairCosetHitMapSetEmbeddingFunctionalTableHit
        i₀ row₀ row₁)
  have hH :
      Fintype.card H * 2 ^ m ≤
        2 * Fintype.card (V13RealLinearRowFunctionalTable m) := by
    simpa [H] using
      (v13RealLinearFunctionalTableTargetCosetHit_card_mul_two_pow_le
        ({row₀} : Finset (Fin m)) i₀ row₁ hrow)
  exact (Nat.mul_le_mul_right (2 ^ m) hSle).trans hH

theorem
    v13RealLinearNoTargetFixedPairCosetHitMapSet_card_mul_two_pow_le_equiv
    {m : Nat} (i₀ row₀ row₁ : Fin m)
    (hrow : row₁ ∉ ({row₀} : Finset (Fin m))) :
    Fintype.card
        (V13RealLinearNoTargetFixedPairCosetHitMapSet i₀ row₀ row₁) *
      2 ^ m ≤
    8 * Fintype.card (V13F2LinearEquiv m) := by
  classical
  let S := Fintype.card
    (V13RealLinearNoTargetFixedPairCosetHitMapSet i₀ row₀ row₁)
  let T := Fintype.card (V13RealLinearRowFunctionalTable m)
  let E := Fintype.card (V13F2LinearEquiv m)
  have htable : S * 2 ^ m ≤ 2 * T := by
    simpa [S, T] using
      v13RealLinearNoTargetFixedPairCosetHitMapSet_card_mul_two_pow_le_table
        i₀ row₀ row₁ hrow
  have hT : T ≤ 4 * E := by
    exact v13RealLinearRowFunctionalTable_card_le_four_mul_equiv m
  have hright : 2 * T ≤ 8 * E := by
    nlinarith
  simpa [S, E] using htable.trans hright

noncomputable def
    v13RealLinearNoTargetFixedPairCosetHitMapSetEmbeddingPairSumTarget
    {m : Nat} (i₀ row₀ row₁ : Fin m) :
    V13RealLinearNoTargetFixedPairCosetHitMapSet i₀ row₀ row₁ ↪
      V13RealLinearNoTargetFixedPairSumTargetMapSet i₀ row₀ row₁ where
  toFun A :=
    ⟨A.val,
      (v13RealLinearNoTargetRows_rowFunctionalTargetCosetHit_singleton_pair_sum
        i₀ row₀ row₁ A.val A.property).2⟩
  inj' := by
    intro A₀ A₁ h
    apply Subtype.ext
    exact
      congrArg
        (fun A :
          V13RealLinearNoTargetFixedPairSumTargetMapSet i₀ row₀ row₁ =>
          A.val)
        h

theorem
    v13RealLinearNoTargetFixedPairCosetHitMapSet_card_mul_two_pow_le_noTarget
    {m : Nat} (i₀ row₀ row₁ : Fin m)
    (hrow : row₁ ∉ ({row₀} : Finset (Fin m))) :
    Fintype.card
        (V13RealLinearNoTargetFixedPairCosetHitMapSet i₀ row₀ row₁) *
      2 ^ m ≤
    4 * Fintype.card (V13RealLinearNoTargetRowsMap m i₀) := by
  classical
  let S :=
    Fintype.card
      (V13RealLinearNoTargetFixedPairCosetHitMapSet i₀ row₀ row₁)
  let P :=
    Fintype.card
      (V13RealLinearNoTargetFixedPairSumTargetMapSet i₀ row₀ row₁)
  let N := Fintype.card (V13RealLinearNoTargetRowsMap m i₀)
  have hneq : row₀ ≠ row₁ := by
    intro h
    exact hrow (by simp [h])
  have hSle : S ≤ P := by
    dsimp [S, P]
    exact
      Fintype.card_le_of_embedding
        (v13RealLinearNoTargetFixedPairCosetHitMapSetEmbeddingPairSumTarget
          i₀ row₀ row₁)
  have hP : P * 2 ^ m ≤ 4 * N := by
    simpa [P, N] using
      v13RealLinearNoTargetFixedPairSumTargetMapSet_card_mul_two_pow_le_noTarget
        i₀ row₀ row₁ hneq
  exact (Nat.mul_le_mul_right (2 ^ m) hSle).trans hP

theorem
    v13RealLinearNoTargetBitJunta_fixed_correct_card_eq_incorrect_card_of_not_blocked
    {m j : Nat} (i₀ : Fin m)
    (observer : V13RealLinearBitJuntaObserver m j)
    (A : V13RealLinearNoTargetRowsMap m i₀)
    (hnot : ¬ V13RealLinearNoTargetBitJuntaBlockedMap i₀ observer A) :
    Fintype.card
        (V13RealLinearNoTargetBitJuntaFixedCorrect i₀ observer A) =
      Fintype.card
        (V13RealLinearNoTargetBitJuntaFixedIncorrect i₀ observer A) :=
  v13RealLinearBitJunta_correct_card_eq_incorrect_card_of_not_blocked
    observer A.val i₀ hnot

theorem
    v13RealLinearNoTargetBitJunta_fixed_correct_card_mul_two_eq_f2vec_card_of_not_blocked
    {m j : Nat} (i₀ : Fin m)
    (observer : V13RealLinearBitJuntaObserver m j)
    (A : V13RealLinearNoTargetRowsMap m i₀)
    (hnot : ¬ V13RealLinearNoTargetBitJuntaBlockedMap i₀ observer A) :
    Fintype.card
        (V13RealLinearNoTargetBitJuntaFixedCorrect i₀ observer A) * 2 =
      Fintype.card (F2Vec m) := by
  simpa [V13RealLinearNoTargetBitJuntaFixedCorrect,
    V13RealLinearNoTargetBitJuntaBlockedMap] using
    v13RealLinearBitJunta_fixed_correct_card_mul_two_eq_f2vec_card_of_not_blocked
      observer A.val i₀ hnot

noncomputable def v13RealLinearNoTargetBitJuntaFixedSuccess
    {m j : Nat} (i₀ : Fin m)
    (observer : V13RealLinearBitJuntaObserver m j)
    (A : V13RealLinearNoTargetRowsMap m i₀) : Rat :=
  v13RealLinearBitJuntaFixedSuccess observer A.val i₀

theorem
    v13RealLinearNoTargetBitJunta_fixedSuccess_eq_half_of_not_blocked
    {m j : Nat} (i₀ : Fin m)
    (observer : V13RealLinearBitJuntaObserver m j)
    (A : V13RealLinearNoTargetRowsMap m i₀)
    (hnot : ¬ V13RealLinearNoTargetBitJuntaBlockedMap i₀ observer A) :
    v13RealLinearNoTargetBitJuntaFixedSuccess i₀ observer A =
      (1 / 2 : Rat) := by
  simpa [v13RealLinearNoTargetBitJuntaFixedSuccess,
    V13RealLinearNoTargetBitJuntaBlockedMap] using
    v13RealLinearBitJunta_fixedSuccess_eq_half_of_not_blocked
      observer A.val i₀ hnot

def V13RealLinearNoTargetBitJuntaCorrect {m j : Nat}
    (i₀ : Fin m) (observer : V13RealLinearBitJuntaObserver m j) :=
  {omega : V13RealLinearNoTargetRowsWorld m i₀ //
    observer.decide (v13RealLinearNoTargetRowsPublicInput omega) =
      omega.2 i₀}

def V13RealLinearNoTargetBitJuntaIncorrect {m j : Nat}
    (i₀ : Fin m) (observer : V13RealLinearBitJuntaObserver m j) :=
  {omega : V13RealLinearNoTargetRowsWorld m i₀ //
    observer.decide (v13RealLinearNoTargetRowsPublicInput omega) ≠
      omega.2 i₀}

def V13RealLinearNoTargetBitJuntaBlockedWorld {m j : Nat}
    (i₀ : Fin m) (observer : V13RealLinearBitJuntaObserver m j) :=
  {omega : V13RealLinearNoTargetRowsWorld m i₀ //
    V13RealLinearNoTargetBitJuntaBlockedMap i₀ observer omega.1}

noncomputable instance {m j : Nat}
    (i₀ : Fin m) (observer : V13RealLinearBitJuntaObserver m j) :
    Fintype (V13RealLinearNoTargetBitJuntaCorrect i₀ observer) := by
  classical
  unfold V13RealLinearNoTargetBitJuntaCorrect
  infer_instance

noncomputable instance {m j : Nat}
    (i₀ : Fin m) (observer : V13RealLinearBitJuntaObserver m j) :
    Fintype (V13RealLinearNoTargetBitJuntaIncorrect i₀ observer) := by
  classical
  unfold V13RealLinearNoTargetBitJuntaIncorrect
  infer_instance

noncomputable instance {m j : Nat}
    (i₀ : Fin m) (observer : V13RealLinearBitJuntaObserver m j) :
    Fintype (V13RealLinearNoTargetBitJuntaBlockedWorld i₀ observer) := by
  classical
  unfold V13RealLinearNoTargetBitJuntaBlockedWorld
  infer_instance

noncomputable def v13RealLinearNoTargetBitJuntaSuccess {m j : Nat}
    (i₀ : Fin m) (observer : V13RealLinearBitJuntaObserver m j) : Rat :=
  (Fintype.card (V13RealLinearNoTargetBitJuntaCorrect i₀ observer) : Rat) /
    (Fintype.card (V13RealLinearNoTargetRowsWorld m i₀) : Rat)

/-- Division-free form of the second-rung counting target.  It says the
fraction of no-target maps whose RHS-read rows block the target is at most
`eps2(j,m) = 4 * 2^j / 2^m`. -/
def V13RealLinearNoTargetBitJuntaBlockedCountingBound
    (m j : Nat) : Prop := by
  classical
  exact
    ∀ (i₀ : Fin m) (observer : V13RealLinearBitJuntaObserver m j),
      (2 ^ m) *
          Fintype.card
            (V13RealLinearNoTargetBitJuntaBlockedMapSet i₀ observer) ≤
        4 * (2 ^ j) *
          Fintype.card (V13RealLinearNoTargetRowsMap m i₀)

theorem
    V13RealLinearNoTargetBitJuntaBlockedCountingBound_of_budgetedRowsetGeneration
    {m j : Nat}
    (hcount : V13RealLinearNoTargetBudgetedRowsetGenerationCountingBound m j) :
    V13RealLinearNoTargetBitJuntaBlockedCountingBound m j := by
  intro i₀ observer
  have h :=
    hcount i₀ (v13RealLinearBitJuntaRhsBudgetedRowset observer)
  rw [
    v13RealLinearNoTargetBitJuntaBlockedMapSet_card_eq_budgetedGeneratingMapSet
      i₀ observer]
  exact h

def V13RealLinearNoTargetBitJuntaSuccessBound
    (m j : Nat) : Prop :=
  ∀ (i₀ : Fin m) (observer : V13RealLinearBitJuntaObserver m j),
    v13RealLinearNoTargetBitJuntaSuccess i₀ observer ≤
      (1 / 2 : Rat) + v13RealLinearBitJuntaEpsilon2 j m

def V13RealLinearNoTargetBitJuntaUnblockedCorrect {m j : Nat}
    (i₀ : Fin m) (observer : V13RealLinearBitJuntaObserver m j) :=
  {omega : V13RealLinearNoTargetRowsWorld m i₀ //
    observer.decide (v13RealLinearNoTargetRowsPublicInput omega) =
      omega.2 i₀ ∧
    ¬ V13RealLinearNoTargetBitJuntaBlockedMap i₀ observer omega.1}

noncomputable instance {m j : Nat}
    (i₀ : Fin m) (observer : V13RealLinearBitJuntaObserver m j) :
    Fintype (V13RealLinearNoTargetBitJuntaUnblockedCorrect i₀ observer) := by
  classical
  unfold V13RealLinearNoTargetBitJuntaUnblockedCorrect
  infer_instance

noncomputable def v13RealLinearNoTargetBitJuntaFlipWitness
    {m j : Nat} (i₀ : Fin m)
    (observer : V13RealLinearBitJuntaObserver m j)
    (A : V13RealLinearNoTargetRowsMap m i₀) : F2Vec m := by
  classical
  exact
    if hnot :
        ¬ V13RealLinearNoTargetBitJuntaBlockedMap i₀ observer A then
      Classical.choose
        (v13RealLinear_exists_kernel_hit_of_not_rowsBlockTarget
          (A := A.val) (rows := v13RealLinearBitJuntaRhsRows observer)
          (i₀ := i₀) hnot)
    else
      f2ZeroVec m

lemma v13RealLinearNoTargetBitJuntaFlipWitness_target
    {m j : Nat} (i₀ : Fin m)
    (observer : V13RealLinearBitJuntaObserver m j)
    (A : V13RealLinearNoTargetRowsMap m i₀)
    (hnot :
      ¬ V13RealLinearNoTargetBitJuntaBlockedMap i₀ observer A) :
    v13RealLinearNoTargetBitJuntaFlipWitness i₀ observer A i₀ = 1 := by
  unfold v13RealLinearNoTargetBitJuntaFlipWitness
  classical
  simpa [hnot] using
    (Classical.choose_spec
      (v13RealLinear_exists_kernel_hit_of_not_rowsBlockTarget
        (A := A.val) (rows := v13RealLinearBitJuntaRhsRows observer)
        (i₀ := i₀) hnot)).1

lemma v13RealLinearNoTargetBitJuntaFlipWitness_kernel
    {m j : Nat} (i₀ : Fin m)
    (observer : V13RealLinearBitJuntaObserver m j)
    (A : V13RealLinearNoTargetRowsMap m i₀)
    (hnot :
      ¬ V13RealLinearNoTargetBitJuntaBlockedMap i₀ observer A) :
    ∀ row : Fin m, row ∈ v13RealLinearBitJuntaRhsRows observer →
      A.val.toEquiv
          (v13RealLinearNoTargetBitJuntaFlipWitness i₀ observer A) row =
        0 := by
  unfold v13RealLinearNoTargetBitJuntaFlipWitness
  classical
  simpa [hnot] using
    (Classical.choose_spec
      (v13RealLinear_exists_kernel_hit_of_not_rowsBlockTarget
        (A := A.val) (rows := v13RealLinearBitJuntaRhsRows observer)
        (i₀ := i₀) hnot)).2

noncomputable def
    v13RealLinearNoTargetBitJuntaUnblockedCorrectToIncorrect
    {m j : Nat} (i₀ : Fin m)
    (observer : V13RealLinearBitJuntaObserver m j) :
    V13RealLinearNoTargetBitJuntaUnblockedCorrect i₀ observer ↪
      V13RealLinearNoTargetBitJuntaIncorrect i₀ observer where
  toFun omega :=
    let A := omega.val.1
    let w := v13RealLinearNoTargetBitJuntaFlipWitness i₀ observer A
    ⟨(A, f2AddVec omega.val.2 w), by
      have hnot :
          ¬ V13RealLinearNoTargetBitJuntaBlockedMap i₀ observer A :=
        omega.property.2
      have hkernel :
          ∀ row : Fin m, row ∈ v13RealLinearBitJuntaRhsRows observer →
            A.val.toEquiv w row = 0 :=
        v13RealLinearNoTargetBitJuntaFlipWitness_kernel
          i₀ observer A hnot
      have hdec :=
        v13RealLinearBitJunta_decide_same_after_kernel_add
          observer A.val omega.val.2 w hkernel
      have htargetNe :
          v13RealLinearTarget i₀
              ({ x := f2AddVec omega.val.2 w, A := A.val } :
                V13RealLinearWorld m) ≠
            v13RealLinearTarget i₀
              ({ x := omega.val.2, A := A.val } :
                V13RealLinearWorld m) :=
        v13RealLinear_target_changes_after_kernel_hit
          A.val omega.val.2 w
          (v13RealLinearNoTargetBitJuntaFlipWitness_target
            i₀ observer A hnot)
      intro hbad
      apply htargetNe
      calc
        v13RealLinearTarget i₀
            ({ x := f2AddVec omega.val.2 w, A := A.val } :
              V13RealLinearWorld m) =
          observer.decide
            (v13RealLinearNoTargetRowsPublicInput
              (A, f2AddVec omega.val.2 w)) := hbad.symm
        _ = observer.decide
            (v13RealLinearNoTargetRowsPublicInput omega.val) := by
              simpa [v13RealLinearNoTargetRowsPublicInput] using hdec.symm
        _ = v13RealLinearTarget i₀
            ({ x := omega.val.2, A := A.val } :
              V13RealLinearWorld m) := by
              simpa [v13RealLinearTarget] using omega.property.1⟩
  inj' := by
    intro omega₀ omega₁ hmap
    apply Subtype.ext
    let A₀ := omega₀.val.1
    let A₁ := omega₁.val.1
    let w₀ := v13RealLinearNoTargetBitJuntaFlipWitness i₀ observer A₀
    let w₁ := v13RealLinearNoTargetBitJuntaFlipWitness i₀ observer A₁
    have hpair :
        (A₀, f2AddVec omega₀.val.2 w₀) =
          (A₁, f2AddVec omega₁.val.2 w₁) := by
      exact congrArg Subtype.val hmap
    have hA : A₀ = A₁ := by
      injection hpair
    have hxflip :
        f2AddVec omega₀.val.2 w₀ =
          f2AddVec omega₁.val.2 w₁ := by
      injection hpair
    have hw : w₀ = w₁ := by
      dsimp [w₀, w₁]
      rw [hA]
    apply Prod.ext
    · exact hA
    · funext row
      have hxpoint := congrFun hxflip row
      rw [hw] at hxpoint
      simp [f2AddVec] at hxpoint ⊢
      calc
        omega₀.val.2 row =
            omega₀.val.2 row + w₁ row + w₁ row := by
              rw [f2_add_right_self]
        _ = omega₁.val.2 row + w₁ row + w₁ row := by
              rw [hxpoint]
        _ = omega₁.val.2 row := by
              rw [f2_add_right_self]

noncomputable def
    v13RealLinearNoTargetBitJuntaCorrectToUnblockedOrBlocked
    {m j : Nat} (i₀ : Fin m)
    (observer : V13RealLinearBitJuntaObserver m j) :
    V13RealLinearNoTargetBitJuntaCorrect i₀ observer ↪
      V13RealLinearNoTargetBitJuntaUnblockedCorrect i₀ observer ⊕
        V13RealLinearNoTargetBitJuntaBlockedWorld i₀ observer where
  toFun omega := by
    classical
    by_cases hblocked :
        V13RealLinearNoTargetBitJuntaBlockedMap i₀ observer omega.val.1
    · exact Sum.inr ⟨omega.val, hblocked⟩
    · exact Sum.inl ⟨omega.val, omega.property, hblocked⟩
  inj' := by
    intro omega₀ omega₁ hmap
    classical
    by_cases hblocked₀ :
        V13RealLinearNoTargetBitJuntaBlockedMap i₀ observer omega₀.val.1 <;>
      by_cases hblocked₁ :
        V13RealLinearNoTargetBitJuntaBlockedMap i₀ observer omega₁.val.1 <;>
      simp [hblocked₀, hblocked₁] at hmap
    · exact
        Subtype.ext
          (congrArg
            (fun omega :
              V13RealLinearNoTargetBitJuntaBlockedWorld i₀ observer =>
                omega.val)
            hmap)
    · exact
        Subtype.ext
          (congrArg
            (fun omega :
              V13RealLinearNoTargetBitJuntaUnblockedCorrect i₀ observer =>
                omega.val)
            hmap)

noncomputable def
    v13RealLinearNoTargetBitJuntaWorldCorrectIncorrectEquiv
    {m j : Nat} (i₀ : Fin m)
    (observer : V13RealLinearBitJuntaObserver m j) :
    V13RealLinearNoTargetRowsWorld m i₀ ≃
      V13RealLinearNoTargetBitJuntaCorrect i₀ observer ⊕
        V13RealLinearNoTargetBitJuntaIncorrect i₀ observer where
  toFun omega := by
    classical
    by_cases hcorrect :
        observer.decide (v13RealLinearNoTargetRowsPublicInput omega) =
          omega.2 i₀
    · exact Sum.inl ⟨omega, hcorrect⟩
    · exact Sum.inr ⟨omega, hcorrect⟩
  invFun y :=
    Sum.elim
      (fun omega : V13RealLinearNoTargetBitJuntaCorrect i₀ observer =>
        omega.val)
      (fun omega : V13RealLinearNoTargetBitJuntaIncorrect i₀ observer =>
        omega.val)
      y
  left_inv omega := by
    classical
    by_cases hcorrect :
        observer.decide (v13RealLinearNoTargetRowsPublicInput omega) =
          omega.2 i₀ <;> simp [hcorrect]
  right_inv y := by
    classical
    cases y with
    | inl omega =>
        change
          (if hcorrect :
              observer.decide
                  (v13RealLinearNoTargetRowsPublicInput omega.val) =
                omega.val.2 i₀ then
              Sum.inl
                (⟨omega.val, hcorrect⟩ :
                  V13RealLinearNoTargetBitJuntaCorrect i₀ observer)
            else
              Sum.inr
                (⟨omega.val, hcorrect⟩ :
                  V13RealLinearNoTargetBitJuntaIncorrect i₀ observer)) =
            Sum.inl omega
        rw [dif_pos omega.property]
        rfl
    | inr omega =>
        change
          (if hcorrect :
              observer.decide
                  (v13RealLinearNoTargetRowsPublicInput omega.val) =
                omega.val.2 i₀ then
              Sum.inl
                (⟨omega.val, hcorrect⟩ :
                  V13RealLinearNoTargetBitJuntaCorrect i₀ observer)
            else
              Sum.inr
                (⟨omega.val, hcorrect⟩ :
                  V13RealLinearNoTargetBitJuntaIncorrect i₀ observer)) =
            Sum.inr omega
        rw [dif_neg omega.property]
        rfl

theorem
    v13RealLinearNoTargetBitJunta_unblockedCorrect_card_le_incorrect
    {m j : Nat} (i₀ : Fin m)
    (observer : V13RealLinearBitJuntaObserver m j) :
    Fintype.card
        (V13RealLinearNoTargetBitJuntaUnblockedCorrect i₀ observer) ≤
      Fintype.card
        (V13RealLinearNoTargetBitJuntaIncorrect i₀ observer) :=
  Fintype.card_le_of_embedding
    (v13RealLinearNoTargetBitJuntaUnblockedCorrectToIncorrect
      i₀ observer)

theorem
    v13RealLinearNoTargetBitJunta_correct_card_le_incorrect_add_blocked
    {m j : Nat} (i₀ : Fin m)
    (observer : V13RealLinearBitJuntaObserver m j) :
    Fintype.card
        (V13RealLinearNoTargetBitJuntaCorrect i₀ observer) ≤
      Fintype.card
          (V13RealLinearNoTargetBitJuntaIncorrect i₀ observer) +
        Fintype.card
          (V13RealLinearNoTargetBitJuntaBlockedWorld i₀ observer) := by
  have hsplit :
      Fintype.card
          (V13RealLinearNoTargetBitJuntaCorrect i₀ observer) ≤
        Fintype.card
          (V13RealLinearNoTargetBitJuntaUnblockedCorrect i₀ observer ⊕
            V13RealLinearNoTargetBitJuntaBlockedWorld i₀ observer) :=
    Fintype.card_le_of_embedding
      (v13RealLinearNoTargetBitJuntaCorrectToUnblockedOrBlocked
        i₀ observer)
  rw [Fintype.card_sum] at hsplit
  have hunblocked :=
    v13RealLinearNoTargetBitJunta_unblockedCorrect_card_le_incorrect
      i₀ observer
  omega

theorem
    v13RealLinearNoTargetBitJunta_world_card_eq_correct_add_incorrect
    {m j : Nat} (i₀ : Fin m)
    (observer : V13RealLinearBitJuntaObserver m j) :
    Fintype.card (V13RealLinearNoTargetRowsWorld m i₀) =
      Fintype.card
          (V13RealLinearNoTargetBitJuntaCorrect i₀ observer) +
        Fintype.card
          (V13RealLinearNoTargetBitJuntaIncorrect i₀ observer) := by
  simpa [Fintype.card_sum] using
    Fintype.card_congr
      (v13RealLinearNoTargetBitJuntaWorldCorrectIncorrectEquiv
        i₀ observer)

theorem
    v13RealLinearNoTargetBitJunta_correct_card_mul_two_le_world_card_add_blocked_card
    {m j : Nat} (i₀ : Fin m)
    (observer : V13RealLinearBitJuntaObserver m j) :
    Fintype.card (V13RealLinearNoTargetBitJuntaCorrect i₀ observer) * 2 ≤
      Fintype.card (V13RealLinearNoTargetRowsWorld m i₀) +
        Fintype.card
          (V13RealLinearNoTargetBitJuntaBlockedWorld i₀ observer) := by
  let C := Fintype.card (V13RealLinearNoTargetBitJuntaCorrect i₀ observer)
  let I := Fintype.card (V13RealLinearNoTargetBitJuntaIncorrect i₀ observer)
  let B := Fintype.card (V13RealLinearNoTargetBitJuntaBlockedWorld i₀ observer)
  let T := Fintype.card (V13RealLinearNoTargetRowsWorld m i₀)
  have hcardNat : C ≤ I + B := by
    simpa [C, I, B] using
      v13RealLinearNoTargetBitJunta_correct_card_le_incorrect_add_blocked
        i₀ observer
  have hworldNat : T = C + I := by
    simpa [T, C, I] using
      v13RealLinearNoTargetBitJunta_world_card_eq_correct_add_incorrect
        i₀ observer
  omega

noncomputable def v13RealLinearNoTargetBitJuntaBlockedMass {m j : Nat}
    (i₀ : Fin m) (observer : V13RealLinearBitJuntaObserver m j) : Rat :=
  (Fintype.card
      (V13RealLinearNoTargetBitJuntaBlockedWorld i₀ observer) : Rat) /
    (Fintype.card (V13RealLinearNoTargetRowsWorld m i₀) : Rat)

def V13RealLinearNoTargetBitJuntaKernelFlipSurchargeBound
    (m j : Nat) : Prop :=
  ∀ (i₀ : Fin m) (observer : V13RealLinearBitJuntaObserver m j),
    v13RealLinearNoTargetBitJuntaSuccess i₀ observer ≤
      (1 / 2 : Rat) +
        v13RealLinearNoTargetBitJuntaBlockedMass i₀ observer

theorem v13RealLinearNoTargetBitJunta_kernelFlipSurchargeBound
    (m j : Nat) :
    V13RealLinearNoTargetBitJuntaKernelFlipSurchargeBound m j := by
  classical
  intro i₀ observer
  unfold v13RealLinearNoTargetBitJuntaSuccess
  unfold v13RealLinearNoTargetBitJuntaBlockedMass
  let C := Fintype.card (V13RealLinearNoTargetBitJuntaCorrect i₀ observer)
  let I := Fintype.card (V13RealLinearNoTargetBitJuntaIncorrect i₀ observer)
  let B := Fintype.card (V13RealLinearNoTargetBitJuntaBlockedWorld i₀ observer)
  let T := Fintype.card (V13RealLinearNoTargetRowsWorld m i₀)
  have hcardNat : C ≤ I + B := by
    simpa [C, I, B] using
      v13RealLinearNoTargetBitJunta_correct_card_le_incorrect_add_blocked
        i₀ observer
  have hworldNat : T = C + I := by
    simpa [T, C, I] using
      v13RealLinearNoTargetBitJunta_world_card_eq_correct_add_incorrect
        i₀ observer
  change (C : Rat) / (T : Rat) ≤ (1 / 2 : Rat) + (B : Rat) / (T : Rat)
  by_cases hTzero : T = 0
  · simp [hTzero]
  · have hTposNat : 0 < T := Nat.pos_of_ne_zero hTzero
    have hTpos : (0 : Rat) < (T : Rat) := by exact_mod_cast hTposNat
    have hcardRat : (C : Rat) ≤ (I : Rat) + (B : Rat) := by
      exact_mod_cast hcardNat
    have hworldRat : (T : Rat) = (C : Rat) + (I : Rat) := by
      exact_mod_cast hworldNat
    rw [div_le_iff₀ hTpos]
    field_simp [hTpos.ne']
    linarith [hcardRat, hworldRat]

noncomputable def
    v13RealLinearNoTargetBitJuntaBlockedWorldEquivBlockedMapProd
    {m j : Nat} (i₀ : Fin m)
    (observer : V13RealLinearBitJuntaObserver m j) :
    V13RealLinearNoTargetBitJuntaBlockedWorld i₀ observer ≃
      V13RealLinearNoTargetBitJuntaBlockedMapSet i₀ observer ×
        F2Vec m where
  toFun omega := ⟨⟨omega.val.1, omega.property⟩, omega.val.2⟩
  invFun omega := ⟨(omega.1.val, omega.2), omega.1.property⟩
  left_inv omega := by
    rfl
  right_inv omega := by
    rfl

theorem v13RealLinearNoTargetBitJuntaBlockedWorld_card_eq
    {m j : Nat} (i₀ : Fin m)
    (observer : V13RealLinearBitJuntaObserver m j) :
    Fintype.card
        (V13RealLinearNoTargetBitJuntaBlockedWorld i₀ observer) =
      Fintype.card
          (V13RealLinearNoTargetBitJuntaBlockedMapSet i₀ observer) *
        Fintype.card (F2Vec m) := by
  classical
  rw [Fintype.card_congr
    (v13RealLinearNoTargetBitJuntaBlockedWorldEquivBlockedMapProd
      i₀ observer)]
  simp [Fintype.card_prod]

theorem
    realLinearNoTargetBitJuntaBlockedWorld_card_mul_two_pow_le_world
    {m j : Nat} (i₀ : Fin m)
    (observer : V13RealLinearBitJuntaObserver m j) :
    Fintype.card
        (V13RealLinearNoTargetBitJuntaBlockedWorld i₀ observer) *
      2 ^ m ≤
    4 * 2 ^ j *
      Fintype.card (V13RealLinearNoTargetRowsWorld m i₀) := by
  classical
  rw [v13RealLinearNoTargetBitJuntaBlockedWorld_card_eq i₀ observer]
  rw [v13RealLinear_f2vec_card]
  let B := Fintype.card
    (V13RealLinearNoTargetBitJuntaBlockedMapSet i₀ observer)
  let N := Fintype.card (V13RealLinearNoTargetRowsMap m i₀)
  let M := 2 ^ m
  let Q := 4 * 2 ^ j
  have hcount :
      M * B ≤ Q * N := by
    have hblocked :
        V13RealLinearNoTargetBitJuntaBlockedCountingBound m j :=
      V13RealLinearNoTargetBitJuntaBlockedCountingBound_of_budgetedRowsetGeneration
        (V13RealLinearNoTargetBudgetedRowsetGenerationCountingBound_allBudget m j)
    simpa [B, N, M, Q, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      using hblocked i₀ observer
  have hmul :
      (B * M) * M ≤ (Q * N) * M := by
    exact
      Nat.mul_le_mul_right M
        (by
          simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
            hcount)
  have hworld :
      Fintype.card (V13RealLinearNoTargetRowsWorld m i₀) = N * M := by
    dsimp [V13RealLinearNoTargetRowsWorld, N, M]
    rw [Fintype.card_prod, v13RealLinear_f2vec_card]
  simpa [B, N, M, Q, hworld, Nat.mul_comm, Nat.mul_left_comm,
    Nat.mul_assoc] using hmul

theorem
    v13RealLinearNoTargetBitJuntaBlockedMass_le_epsilon2_of_counting
    {m j : Nat}
    (hcount : V13RealLinearNoTargetBitJuntaBlockedCountingBound m j)
    (i₀ : Fin m) (observer : V13RealLinearBitJuntaObserver m j) :
    v13RealLinearNoTargetBitJuntaBlockedMass i₀ observer ≤
      v13RealLinearBitJuntaEpsilon2 j m := by
  classical
  unfold v13RealLinearNoTargetBitJuntaBlockedMass
  unfold v13RealLinearBitJuntaEpsilon2
  rw [v13RealLinearNoTargetBitJuntaBlockedWorld_card_eq i₀ observer]
  rw [Fintype.card_prod, v13RealLinear_f2vec_card]
  let B := Fintype.card
    (V13RealLinearNoTargetBitJuntaBlockedMapSet i₀ observer)
  let T := Fintype.card (V13RealLinearNoTargetRowsMap m i₀)
  let M := 2 ^ m
  let Q := 4 * 2 ^ j
  have hcard : M * B ≤ Q * T := by
    simpa [B, T, M, Q, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      using hcount i₀ observer
  have hMposNat : 0 < M := by
    dsimp [M]
    positivity
  have hMpos : (0 : Rat) < (M : Rat) := by
    exact_mod_cast hMposNat
  have hcardRat : (M : Rat) * (B : Rat) ≤ (Q : Rat) * (T : Rat) := by
    exact_mod_cast hcard
  have hQrat : (4 : Rat) * (2 : Rat) ^ j = (Q : Rat) := by
    dsimp [Q]
    norm_num
  have hMrat : (2 : Rat) ^ m = (M : Rat) := by
    dsimp [M]
    norm_num
  rw [hQrat, hMrat]
  change ((B * M : Nat) : Rat) / ((T * M : Nat) : Rat) ≤
    (Q : Rat) / (M : Rat)
  rw [Nat.cast_mul, Nat.cast_mul]
  by_cases hTzero : T = 0
  · have hB_le_T : B ≤ T := by
      dsimp [B, T]
      exact
        Fintype.card_subtype_le
          (fun A : V13RealLinearNoTargetRowsMap m i₀ =>
            V13RealLinearNoTargetBitJuntaBlockedMap i₀ observer A)
    have hBzero : B = 0 :=
      Nat.eq_zero_of_le_zero (by simpa [hTzero] using hB_le_T)
    have hnonneg : 0 ≤ (Q : Rat) / (M : Rat) := by
      positivity
    simpa [hBzero, hTzero] using hnonneg
  · have hTposNat : 0 < T := Nat.pos_of_ne_zero hTzero
    have hTpos : (0 : Rat) < (T : Rat) := by
      exact_mod_cast hTposNat
    field_simp [hTpos.ne', hMpos.ne']
    simpa [mul_comm, mul_left_comm, mul_assoc] using hcardRat

theorem v13RealLinearNoTargetBitJuntaSuccessBound_of_blockedCounting
    {m j : Nat}
    (hcount : V13RealLinearNoTargetBitJuntaBlockedCountingBound m j) :
    V13RealLinearNoTargetBitJuntaSuccessBound m j := by
  intro i₀ observer
  have hflip :=
    v13RealLinearNoTargetBitJunta_kernelFlipSurchargeBound m j i₀ observer
  have hblocked :=
    v13RealLinearNoTargetBitJuntaBlockedMass_le_epsilon2_of_counting
      hcount i₀ observer
  linarith

theorem v13RealLinearNoTargetBitJuntaSuccessBound_of_budgetedRowsetGeneration
    {m j : Nat}
    (hcount : V13RealLinearNoTargetBudgetedRowsetGenerationCountingBound m j) :
    V13RealLinearNoTargetBitJuntaSuccessBound m j :=
  v13RealLinearNoTargetBitJuntaSuccessBound_of_blockedCounting
    (V13RealLinearNoTargetBitJuntaBlockedCountingBound_of_budgetedRowsetGeneration
      hcount)

theorem v13RealLinearNoTargetBitJuntaSuccessBound_zeroBudget (m : Nat) :
    V13RealLinearNoTargetBitJuntaSuccessBound m 0 :=
  v13RealLinearNoTargetBitJuntaSuccessBound_of_budgetedRowsetGeneration
    (V13RealLinearNoTargetBudgetedRowsetGenerationCountingBound_zeroBudget m)

theorem v13RealLinearNoTargetBitJuntaSuccessBound_oneBudget (m : Nat) :
    V13RealLinearNoTargetBitJuntaSuccessBound m 1 :=
  v13RealLinearNoTargetBitJuntaSuccessBound_of_budgetedRowsetGeneration
    (V13RealLinearNoTargetBudgetedRowsetGenerationCountingBound_oneBudget m)

theorem v13RealLinearNoTargetBitJuntaSuccessBound_twoBudget (m : Nat) :
    V13RealLinearNoTargetBitJuntaSuccessBound m 2 :=
  v13RealLinearNoTargetBitJuntaSuccessBound_of_budgetedRowsetGeneration
    (V13RealLinearNoTargetBudgetedRowsetGenerationCountingBound_twoBudget m)

theorem v13RealLinearNoTargetBitJuntaSuccessBound_allBudget (m j : Nat) :
    V13RealLinearNoTargetBitJuntaSuccessBound m j :=
  v13RealLinearNoTargetBitJuntaSuccessBound_of_budgetedRowsetGeneration
    (V13RealLinearNoTargetBudgetedRowsetGenerationCountingBound_allBudget m j)

theorem realLinearNoTargetBitJunta_success_le_half_add_epsilon2
    {m j : Nat} (i₀ : Fin m)
    (observer : V13RealLinearBitJuntaObserver m j) :
    v13RealLinearNoTargetBitJuntaSuccess i₀ observer ≤
      (1 / 2 : Rat) + v13RealLinearBitJuntaEpsilon2 j m :=
  v13RealLinearNoTargetBitJuntaSuccessBound_allBudget m j i₀ observer

lemma v13_zmod2_eq_of_one_add_ne {a b : ZMod 2}
    (h : 1 + a ≠ b) : a = b := by
  refine
    v13_zmod2_eq_of_ne_left
      (a := a) (b := 1 + a) (c := b) ?_ ?_
  · intro hb
    exact h hb.symm
  · intro ha
    have hself : a + 1 = a := by
      calc
        a + 1 = 1 + a := by rw [add_comm]
        _ = a := ha.symm
    exact v13_zmod2_add_one_ne_self a hself

lemma v13_zmod2_add_eq_zero_iff_eq {a b : ZMod 2} :
    a + b = 0 ↔ a = b := by
  constructor
  · intro h
    rcases v13_zmod2_cases a with ha | ha <;>
      rcases v13_zmod2_cases b with hb | hb <;>
        simp [ha, hb] at h ⊢
  · intro h
    rw [h]
    exact f2_add_self b

lemma v13_zmod2_add_eq_one_of_ne {a b : ZMod 2}
    (h : a ≠ b) : a + b = 1 := by
  rcases v13_zmod2_cases a with ha | ha <;>
    rcases v13_zmod2_cases b with hb | hb <;>
      simp [ha, hb] at h ⊢

/-- A parity observer is the XOR of the listed elementary public coordinates. -/
structure V13RealLinearParityObserver (m j : Nat) where
  coordinate : Fin j → Option (V13RealLinearPublicCoordinate m)

noncomputable def V13RealLinearParityObserver.value {m j : Nat}
    (observer : V13RealLinearParityObserver m j)
    (publicInput : V13RealLinearPublic m) : ZMod 2 :=
  ∑ k : Fin j,
    match observer.coordinate k with
    | none => 0
    | some coord => v13RealLinearCoordinateValue coord publicInput

noncomputable def V13RealLinearParityObserver.toBitJunta {m j : Nat}
    (observer : V13RealLinearParityObserver m j) :
    V13RealLinearBitJuntaObserver m j where
  coordinate := observer.coordinate
  decide := observer.value
  factorsThrough := by
    intro public₀ public₁ hsame
    unfold V13RealLinearParityObserver.value
    apply Finset.sum_congr rfl
    intro k _hk
    cases hcoord : observer.coordinate k with
    | none => rfl
    | some coord =>
        simpa [hcoord] using hsame k coord hcoord

noncomputable def v13RealLinearParityObserverConstantTerm {m : Nat}
    (A : V13F2LinearEquiv m)
    (coord : Option (V13RealLinearPublicCoordinate m)) : ZMod 2 :=
  match coord with
  | some (.mapValue probe row) => A.toEquiv probe row
  | some (.inverseValue probe row) => A.toEquiv.symm probe row
  | some (.rhs _row) => 0
  | none => 0

noncomputable def v13RealLinearParityObserverRhsTerm {m : Nat}
    (A : V13F2LinearEquiv m) (x : F2Vec m)
    (coord : Option (V13RealLinearPublicCoordinate m)) : ZMod 2 :=
  match coord with
  | some (.rhs row) => A.toEquiv x row
  | some (.mapValue _probe _row) => 0
  | some (.inverseValue _probe _row) => 0
  | none => 0

noncomputable def v13RealLinearParityObserverConstant {m j : Nat}
    (observer : V13RealLinearParityObserver m j)
    (A : V13F2LinearEquiv m) : ZMod 2 :=
  ∑ k : Fin j,
    v13RealLinearParityObserverConstantTerm A (observer.coordinate k)

noncomputable def v13RealLinearParityObserverRhsParity {m j : Nat}
    (observer : V13RealLinearParityObserver m j)
    (A : V13F2LinearEquiv m) (x : F2Vec m) : ZMod 2 :=
  ∑ k : Fin j,
    v13RealLinearParityObserverRhsTerm A x (observer.coordinate k)

theorem v13RealLinearParityObserver_value_publicInput_eq
    {m j : Nat} (observer : V13RealLinearParityObserver m j)
    (A : V13F2LinearEquiv m) (x : F2Vec m) :
    observer.value
        (v13RealLinearPublicInput
          ({ x := x, A := A } : V13RealLinearWorld m)) =
      v13RealLinearParityObserverConstant observer A +
        v13RealLinearParityObserverRhsParity observer A x := by
  classical
  unfold V13RealLinearParityObserver.value
    v13RealLinearParityObserverConstant
    v13RealLinearParityObserverRhsParity
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _hk
  cases hcoord : observer.coordinate k with
  | none =>
      simp [v13RealLinearParityObserverConstantTerm,
        v13RealLinearParityObserverRhsTerm]
  | some coord =>
      cases coord <;>
        simp [v13RealLinearParityObserverConstantTerm,
          v13RealLinearParityObserverRhsTerm, v13RealLinearCoordinateValue,
          v13RealLinearPublicInput]

theorem v13RealLinearParityObserver_rhsParity_zero
    {m j : Nat} (observer : V13RealLinearParityObserver m j)
    (A : V13F2LinearEquiv m) :
    v13RealLinearParityObserverRhsParity observer A (f2ZeroVec m) = 0 := by
  classical
  unfold v13RealLinearParityObserverRhsParity
  apply Finset.sum_eq_zero
  intro k _hk
  cases hcoord : observer.coordinate k with
  | none =>
      simp [v13RealLinearParityObserverRhsTerm]
  | some coord =>
      cases coord <;>
        simp [v13RealLinearParityObserverRhsTerm, A.map_zero,
          f2ZeroVec]

theorem v13RealLinearParityObserver_rhsParity_add
    {m j : Nat} (observer : V13RealLinearParityObserver m j)
    (A : V13F2LinearEquiv m) (x w : F2Vec m) :
    v13RealLinearParityObserverRhsParity observer A (f2AddVec x w) =
      v13RealLinearParityObserverRhsParity observer A x +
        v13RealLinearParityObserverRhsParity observer A w := by
  classical
  unfold v13RealLinearParityObserverRhsParity
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _hk
  cases hcoord : observer.coordinate k with
  | none =>
      simp [v13RealLinearParityObserverRhsTerm]
  | some coord =>
      cases coord with
      | rhs row =>
          simpa [v13RealLinearParityObserverRhsTerm, f2AddVec]
            using congrFun (A.map_add x w) row
      | mapValue probe row =>
          simp [v13RealLinearParityObserverRhsTerm]
      | inverseValue probe row =>
          simp [v13RealLinearParityObserverRhsTerm]

theorem v13RealLinearParityObserver_value_after_add
    {m j : Nat} (observer : V13RealLinearParityObserver m j)
    (A : V13F2LinearEquiv m) (x w : F2Vec m) :
    observer.value
        (v13RealLinearPublicInput
          ({ x := f2AddVec x w, A := A } : V13RealLinearWorld m)) =
      observer.value
          (v13RealLinearPublicInput
            ({ x := x, A := A } : V13RealLinearWorld m)) +
        v13RealLinearParityObserverRhsParity observer A w := by
  have hflip :=
    v13RealLinearParityObserver_value_publicInput_eq
      observer A (f2AddVec x w)
  have hx :=
    v13RealLinearParityObserver_value_publicInput_eq observer A x
  have hlin :=
    v13RealLinearParityObserver_rhsParity_add observer A x w
  calc
    observer.value
        (v13RealLinearPublicInput
          ({ x := f2AddVec x w, A := A } : V13RealLinearWorld m)) =
        v13RealLinearParityObserverConstant observer A +
          v13RealLinearParityObserverRhsParity observer A (f2AddVec x w) :=
          hflip
    _ =
        v13RealLinearParityObserverConstant observer A +
          (v13RealLinearParityObserverRhsParity observer A x +
            v13RealLinearParityObserverRhsParity observer A w) := by
          rw [hlin]
    _ =
        (v13RealLinearParityObserverConstant observer A +
          v13RealLinearParityObserverRhsParity observer A x) +
            v13RealLinearParityObserverRhsParity observer A w := by
          rw [add_assoc]
    _ =
        observer.value
          (v13RealLinearPublicInput
            ({ x := x, A := A } : V13RealLinearWorld m)) +
          v13RealLinearParityObserverRhsParity observer A w := by
          rw [← hx]

theorem v13RealLinearParityObserver_value_target_delta_after_add
    {m j : Nat} (observer : V13RealLinearParityObserver m j)
    (A : V13F2LinearEquiv m) (i₀ : Fin m) (x w : F2Vec m) :
    observer.value
        (v13RealLinearPublicInput
          ({ x := f2AddVec x w, A := A } : V13RealLinearWorld m)) +
      (f2AddVec x w) i₀ =
        (observer.value
          (v13RealLinearPublicInput
            ({ x := x, A := A } : V13RealLinearWorld m)) +
          x i₀) +
        (v13RealLinearParityObserverRhsParity observer A w + w i₀) := by
  rw [v13RealLinearParityObserver_value_after_add observer A x w]
  simp [f2AddVec]
  ring

def V13RealLinearParityObserverRhsParityMatchesTarget {m j : Nat}
    (observer : V13RealLinearParityObserver m j)
    (A : V13F2LinearEquiv m) (i₀ : Fin m) : Prop :=
  ∀ x : F2Vec m,
    v13RealLinearParityObserverRhsParity observer A x = x i₀

def V13RealLinearParityObserverDeterminesTarget {m j : Nat}
    (observer : V13RealLinearParityObserver m j)
    (A : V13F2LinearEquiv m) (i₀ : Fin m) : Prop :=
  ∀ x : F2Vec m,
    observer.value
        (v13RealLinearPublicInput
          ({ x := x, A := A } : V13RealLinearWorld m)) =
      x i₀

def V13RealLinearParityObserverDeterminesTargetComplement {m j : Nat}
    (observer : V13RealLinearParityObserver m j)
    (A : V13F2LinearEquiv m) (i₀ : Fin m) : Prop :=
  ∀ x : F2Vec m,
    observer.value
        (v13RealLinearPublicInput
          ({ x := x, A := A } : V13RealLinearWorld m)) ≠
      x i₀

theorem v13RealLinearParityObserver_determinesTarget_iff
    {m j : Nat} (observer : V13RealLinearParityObserver m j)
    (A : V13F2LinearEquiv m) (i₀ : Fin m) :
    V13RealLinearParityObserverDeterminesTarget observer A i₀ ↔
      v13RealLinearParityObserverConstant observer A = 0 ∧
        V13RealLinearParityObserverRhsParityMatchesTarget
          observer A i₀ := by
  constructor
  · intro h
    have hzeroValue := h (f2ZeroVec m)
    have hdecomp :=
      v13RealLinearParityObserver_value_publicInput_eq
        observer A (f2ZeroVec m)
    have hrhsZero :=
      v13RealLinearParityObserver_rhsParity_zero observer A
    have hconst : v13RealLinearParityObserverConstant observer A = 0 := by
      calc
        v13RealLinearParityObserverConstant observer A =
            v13RealLinearParityObserverConstant observer A +
              v13RealLinearParityObserverRhsParity
                observer A (f2ZeroVec m) := by
              rw [hrhsZero, add_zero]
        _ = observer.value
              (v13RealLinearPublicInput
                ({ x := f2ZeroVec m, A := A } :
                  V13RealLinearWorld m)) := hdecomp.symm
        _ = (f2ZeroVec m) i₀ := hzeroValue
        _ = 0 := by simp [f2ZeroVec]
    refine ⟨hconst, ?_⟩
    intro x
    have hx := h x
    have hdx :=
      v13RealLinearParityObserver_value_publicInput_eq observer A x
    calc
      v13RealLinearParityObserverRhsParity observer A x =
          v13RealLinearParityObserverConstant observer A +
            v13RealLinearParityObserverRhsParity observer A x := by
            rw [hconst, zero_add]
      _ = observer.value
            (v13RealLinearPublicInput
              ({ x := x, A := A } : V13RealLinearWorld m)) := hdx.symm
      _ = x i₀ := hx
  · rintro ⟨hconst, hmatch⟩ x
    have hdx :=
      v13RealLinearParityObserver_value_publicInput_eq observer A x
    calc
      observer.value
          (v13RealLinearPublicInput
            ({ x := x, A := A } : V13RealLinearWorld m)) =
          v13RealLinearParityObserverConstant observer A +
            v13RealLinearParityObserverRhsParity observer A x := hdx
      _ = x i₀ := by rw [hconst, zero_add, hmatch x]

theorem v13RealLinearParityObserver_determinesTargetComplement_iff
    {m j : Nat} (observer : V13RealLinearParityObserver m j)
    (A : V13F2LinearEquiv m) (i₀ : Fin m) :
    V13RealLinearParityObserverDeterminesTargetComplement observer A i₀ ↔
      v13RealLinearParityObserverConstant observer A = 1 ∧
        V13RealLinearParityObserverRhsParityMatchesTarget
          observer A i₀ := by
  constructor
  · intro h
    have hzeroNe := h (f2ZeroVec m)
    have hdecomp :=
      v13RealLinearParityObserver_value_publicInput_eq
        observer A (f2ZeroVec m)
    have hrhsZero :=
      v13RealLinearParityObserver_rhsParity_zero observer A
    have hconstNe :
        v13RealLinearParityObserverConstant observer A ≠ 0 := by
      intro hzero
      apply hzeroNe
      calc
        observer.value
            (v13RealLinearPublicInput
              ({ x := f2ZeroVec m, A := A } :
                V13RealLinearWorld m)) =
            v13RealLinearParityObserverConstant observer A +
              v13RealLinearParityObserverRhsParity
                observer A (f2ZeroVec m) := hdecomp
        _ = 0 := by rw [hzero, hrhsZero, zero_add]
        _ = (f2ZeroVec m) i₀ := by simp [f2ZeroVec]
    have hconst :
        v13RealLinearParityObserverConstant observer A = 1 :=
      v13_zmod2_eq_one_of_ne_zero _ hconstNe
    refine ⟨hconst, ?_⟩
    intro x
    have hxne := h x
    have hdx :=
      v13RealLinearParityObserver_value_publicInput_eq observer A x
    have honeAddNe :
        1 + v13RealLinearParityObserverRhsParity observer A x ≠
          x i₀ := by
      intro hbad
      apply hxne
      calc
        observer.value
            (v13RealLinearPublicInput
              ({ x := x, A := A } : V13RealLinearWorld m)) =
            v13RealLinearParityObserverConstant observer A +
              v13RealLinearParityObserverRhsParity observer A x := hdx
        _ = 1 + v13RealLinearParityObserverRhsParity observer A x := by
          rw [hconst]
        _ = x i₀ := hbad
    exact v13_zmod2_eq_of_one_add_ne honeAddNe
  · rintro ⟨hconst, hmatch⟩ x
    have hdx :=
      v13RealLinearParityObserver_value_publicInput_eq observer A x
    intro hbad
    have htarget : x i₀ + 1 = x i₀ := by
      calc
        x i₀ + 1 = 1 + x i₀ := by rw [add_comm]
        _ = 1 + v13RealLinearParityObserverRhsParity observer A x := by
          rw [← hmatch x]
        _ = v13RealLinearParityObserverConstant observer A +
              v13RealLinearParityObserverRhsParity observer A x := by
          rw [hconst]
        _ = observer.value
              (v13RealLinearPublicInput
                ({ x := x, A := A } : V13RealLinearWorld m)) := hdx.symm
        _ = x i₀ := hbad
    exact v13_zmod2_add_one_ne_self (x i₀) htarget

noncomputable def
    v13RealLinearParityObserver_fixedCorrectIncorrectEquiv_of_rhsParity_ne_target
    {m j : Nat} (observer : V13RealLinearParityObserver m j)
    (A : V13F2LinearEquiv m) (i₀ : Fin m) (w : F2Vec m)
    (hdiff :
      v13RealLinearParityObserverRhsParity observer A w ≠ w i₀) :
    V13RealLinearBitJuntaFixedCorrect observer.toBitJunta A i₀ ≃
      V13RealLinearBitJuntaFixedIncorrect observer.toBitJunta A i₀ where
  toFun x :=
    ⟨f2AddVec x.val w, by
      intro hflipCorrect
      have hxCorrect :
          observer.value
              (v13RealLinearPublicInput
                ({ x := x.val, A := A } : V13RealLinearWorld m)) =
            x.val i₀ := by
        simpa [V13RealLinearParityObserver.toBitJunta,
          v13RealLinearTarget] using x.property
      have hflipCorrect' :
          observer.value
              (v13RealLinearPublicInput
                ({ x := f2AddVec x.val w, A := A } :
                  V13RealLinearWorld m)) =
            (f2AddVec x.val w) i₀ := by
        simpa [V13RealLinearParityObserver.toBitJunta,
          v13RealLinearTarget] using hflipCorrect
      have hxDelta :
          observer.value
              (v13RealLinearPublicInput
                ({ x := x.val, A := A } : V13RealLinearWorld m)) +
            x.val i₀ = 0 :=
        (v13_zmod2_add_eq_zero_iff_eq).2 hxCorrect
      have hflipDelta :
          observer.value
              (v13RealLinearPublicInput
                ({ x := f2AddVec x.val w, A := A } :
                  V13RealLinearWorld m)) +
            (f2AddVec x.val w) i₀ = 0 :=
        (v13_zmod2_add_eq_zero_iff_eq).2 hflipCorrect'
      have hstep :=
        v13RealLinearParityObserver_value_target_delta_after_add
          observer A i₀ x.val w
      have hdeltaOne :
          v13RealLinearParityObserverRhsParity observer A w + w i₀ = 1 :=
        v13_zmod2_add_eq_one_of_ne hdiff
      have hflipOne :
          observer.value
              (v13RealLinearPublicInput
                ({ x := f2AddVec x.val w, A := A } :
                  V13RealLinearWorld m)) +
            (f2AddVec x.val w) i₀ = 1 := by
        rw [hstep, hxDelta, hdeltaOne]
        norm_num
      rw [hflipDelta] at hflipOne
      norm_num at hflipOne⟩
  invFun x :=
    ⟨f2AddVec x.val w, by
      have hxIncorrect :
          observer.value
              (v13RealLinearPublicInput
                ({ x := x.val, A := A } : V13RealLinearWorld m)) ≠
            x.val i₀ := by
        simpa [V13RealLinearParityObserver.toBitJunta,
          v13RealLinearTarget] using x.property
      have hxDeltaOne :
          observer.value
              (v13RealLinearPublicInput
                ({ x := x.val, A := A } : V13RealLinearWorld m)) +
            x.val i₀ = 1 :=
        v13_zmod2_add_eq_one_of_ne hxIncorrect
      have hstep :=
        v13RealLinearParityObserver_value_target_delta_after_add
          observer A i₀ x.val w
      have hdeltaOne :
          v13RealLinearParityObserverRhsParity observer A w + w i₀ = 1 :=
        v13_zmod2_add_eq_one_of_ne hdiff
      have hflipDelta :
          observer.value
              (v13RealLinearPublicInput
                ({ x := f2AddVec x.val w, A := A } :
                  V13RealLinearWorld m)) +
            (f2AddVec x.val w) i₀ = 0 := by
        rw [hstep, hxDeltaOne, hdeltaOne]
        exact f2_one_add_one
      have hflipCorrect :
          observer.value
              (v13RealLinearPublicInput
                ({ x := f2AddVec x.val w, A := A } :
                  V13RealLinearWorld m)) =
            (f2AddVec x.val w) i₀ :=
        (v13_zmod2_add_eq_zero_iff_eq).1 hflipDelta
      simpa [V13RealLinearParityObserver.toBitJunta,
        v13RealLinearTarget] using hflipCorrect⟩
  left_inv x := by
    apply Subtype.ext
    funext row
    simp [f2AddVec, add_assoc, f2_add_self]
  right_inv x := by
    apply Subtype.ext
    funext row
    simp [f2AddVec, add_assoc, f2_add_self]

theorem
    v13RealLinearParityObserver_fixed_correct_card_eq_incorrect_card_of_not_rhsParityMatchesTarget
    {m j : Nat} (observer : V13RealLinearParityObserver m j)
    (A : V13F2LinearEquiv m) (i₀ : Fin m)
    (hnot :
      ¬ V13RealLinearParityObserverRhsParityMatchesTarget observer A i₀) :
    Fintype.card
        (V13RealLinearBitJuntaFixedCorrect observer.toBitJunta A i₀) =
      Fintype.card
        (V13RealLinearBitJuntaFixedIncorrect observer.toBitJunta A i₀) := by
  classical
  rw [V13RealLinearParityObserverRhsParityMatchesTarget] at hnot
  rw [not_forall] at hnot
  rcases hnot with ⟨w, hdiff⟩
  exact
    Fintype.card_congr
      (v13RealLinearParityObserver_fixedCorrectIncorrectEquiv_of_rhsParity_ne_target
        observer A i₀ w hdiff)

theorem
    v13RealLinearParityObserver_fixed_correct_card_mul_two_eq_f2vec_card_of_not_rhsParityMatchesTarget
    {m j : Nat} (observer : V13RealLinearParityObserver m j)
    (A : V13F2LinearEquiv m) (i₀ : Fin m)
    (hnot :
      ¬ V13RealLinearParityObserverRhsParityMatchesTarget observer A i₀) :
    Fintype.card
        (V13RealLinearBitJuntaFixedCorrect observer.toBitJunta A i₀) * 2 =
      Fintype.card (F2Vec m) := by
  let C :=
    Fintype.card
      (V13RealLinearBitJuntaFixedCorrect observer.toBitJunta A i₀)
  let I :=
    Fintype.card
      (V13RealLinearBitJuntaFixedIncorrect observer.toBitJunta A i₀)
  have hci : C = I := by
    simpa [C, I] using
      v13RealLinearParityObserver_fixed_correct_card_eq_incorrect_card_of_not_rhsParityMatchesTarget
        observer A i₀ hnot
  have hworld :
      Fintype.card (F2Vec m) = C + I := by
    simpa [C, I] using
      v13RealLinearBitJuntaFixedWorld_card_eq_correct_add_incorrect
        observer.toBitJunta A i₀
  omega

noncomputable def v13RealLinearParityObserverFixedSuccess
    {m j : Nat} (observer : V13RealLinearParityObserver m j)
    (A : V13F2LinearEquiv m) (i₀ : Fin m) : Rat :=
  (Fintype.card
      (V13RealLinearBitJuntaFixedCorrect observer.toBitJunta A i₀) : Rat) /
    (Fintype.card (F2Vec m) : Rat)

noncomputable def
    v13RealLinearParityObserver_fixedCorrectEquiv_of_determinesTarget
    {m j : Nat} (observer : V13RealLinearParityObserver m j)
    (A : V13F2LinearEquiv m) (i₀ : Fin m)
    (hdet : V13RealLinearParityObserverDeterminesTarget observer A i₀) :
    F2Vec m ≃
      V13RealLinearBitJuntaFixedCorrect observer.toBitJunta A i₀ where
  toFun x :=
    ⟨x, by
      simpa [V13RealLinearParityObserver.toBitJunta,
        v13RealLinearTarget] using hdet x⟩
  invFun x := x.val
  left_inv x := rfl
  right_inv x := by
    apply Subtype.ext
    rfl

theorem
    v13RealLinearParityObserver_fixed_correct_card_eq_f2vec_card_of_determinesTarget
    {m j : Nat} (observer : V13RealLinearParityObserver m j)
    (A : V13F2LinearEquiv m) (i₀ : Fin m)
    (hdet : V13RealLinearParityObserverDeterminesTarget observer A i₀) :
    Fintype.card
        (V13RealLinearBitJuntaFixedCorrect observer.toBitJunta A i₀) =
      Fintype.card (F2Vec m) := by
  simpa using
    (Fintype.card_congr
      (v13RealLinearParityObserver_fixedCorrectEquiv_of_determinesTarget
        observer A i₀ hdet)).symm

theorem
    v13RealLinearParityObserver_fixed_correct_card_eq_zero_of_determinesTargetComplement
    {m j : Nat} (observer : V13RealLinearParityObserver m j)
    (A : V13F2LinearEquiv m) (i₀ : Fin m)
    (hcomp :
      V13RealLinearParityObserverDeterminesTargetComplement observer A i₀) :
    Fintype.card
        (V13RealLinearBitJuntaFixedCorrect observer.toBitJunta A i₀) = 0 := by
  rw [Fintype.card_eq_zero_iff]
  exact
    ⟨fun x =>
      hcomp x.val
        (by
          simpa [V13RealLinearParityObserver.toBitJunta,
            v13RealLinearTarget] using x.property)⟩

theorem v13RealLinearParityObserver_fixedSuccess_eq_one_of_determinesTarget
    {m j : Nat} (observer : V13RealLinearParityObserver m j)
    (A : V13F2LinearEquiv m) (i₀ : Fin m)
    (hdet : V13RealLinearParityObserverDeterminesTarget observer A i₀) :
    v13RealLinearParityObserverFixedSuccess observer A i₀ = 1 := by
  classical
  unfold v13RealLinearParityObserverFixedSuccess
  rw [
    v13RealLinearParityObserver_fixed_correct_card_eq_f2vec_card_of_determinesTarget
      observer A i₀ hdet]
  have hcardPosNat : 0 < Fintype.card (F2Vec m) := by
    rw [v13RealLinear_f2vec_card]
    positivity
  have hcardPos : (0 : Rat) < (Fintype.card (F2Vec m) : Rat) := by
    exact_mod_cast hcardPosNat
  field_simp [hcardPos.ne']

theorem
    v13RealLinearParityObserver_fixedSuccess_eq_zero_of_determinesTargetComplement
    {m j : Nat} (observer : V13RealLinearParityObserver m j)
    (A : V13F2LinearEquiv m) (i₀ : Fin m)
    (hcomp :
      V13RealLinearParityObserverDeterminesTargetComplement observer A i₀) :
    v13RealLinearParityObserverFixedSuccess observer A i₀ = 0 := by
  unfold v13RealLinearParityObserverFixedSuccess
  rw [
    v13RealLinearParityObserver_fixed_correct_card_eq_zero_of_determinesTargetComplement
      observer A i₀ hcomp]
  simp

theorem
    v13RealLinearParityObserver_fixedSuccess_eq_half_of_not_rhsParityMatchesTarget
    {m j : Nat} (observer : V13RealLinearParityObserver m j)
    (A : V13F2LinearEquiv m) (i₀ : Fin m)
    (hnot :
      ¬ V13RealLinearParityObserverRhsParityMatchesTarget observer A i₀) :
    v13RealLinearParityObserverFixedSuccess observer A i₀ = (1 / 2 : Rat) := by
  classical
  unfold v13RealLinearParityObserverFixedSuccess
  let C :=
    Fintype.card
      (V13RealLinearBitJuntaFixedCorrect observer.toBitJunta A i₀)
  let T := Fintype.card (F2Vec m)
  have hcardNat : C * 2 = T := by
    simpa [C, T] using
      v13RealLinearParityObserver_fixed_correct_card_mul_two_eq_f2vec_card_of_not_rhsParityMatchesTarget
        observer A i₀ hnot
  have hcardRat : (C : Rat) * 2 = (T : Rat) := by
    exact_mod_cast hcardNat
  have hTposNat : 0 < T := by
    dsimp [T]
    rw [v13RealLinear_f2vec_card]
    positivity
  have hTpos : (0 : Rat) < (T : Rat) := by
    exact_mod_cast hTposNat
  change (C : Rat) / (T : Rat) = (1 / 2 : Rat)
  field_simp [hTpos.ne']
  linarith

theorem
    realLinearNoTargetParityObserver_fixedSuccess_eq_half_of_not_rhsParityMatchesTarget
    {m j : Nat} (observer : V13RealLinearParityObserver m j)
    (i₀ : Fin m) (A : V13RealLinearNoTargetRowsMap m i₀)
    (hnot :
      ¬ V13RealLinearParityObserverRhsParityMatchesTarget observer A.val i₀) :
    v13RealLinearNoTargetBitJuntaFixedSuccess i₀ observer.toBitJunta A =
      (1 / 2 : Rat) := by
  simpa [v13RealLinearNoTargetBitJuntaFixedSuccess,
    v13RealLinearParityObserverFixedSuccess,
    v13RealLinearBitJuntaFixedSuccess, v13RealLinear_f2vec_card] using
    v13RealLinearParityObserver_fixedSuccess_eq_half_of_not_rhsParityMatchesTarget
      observer A.val i₀ hnot

theorem v13RealLinearParityObserver_fixedSuccess_trichotomy
    {m j : Nat} (observer : V13RealLinearParityObserver m j)
    (A : V13F2LinearEquiv m) (i₀ : Fin m) :
    (V13RealLinearParityObserverDeterminesTarget observer A i₀ ∧
        v13RealLinearParityObserverFixedSuccess observer A i₀ = 1) ∨
      (V13RealLinearParityObserverDeterminesTargetComplement observer A i₀ ∧
        v13RealLinearParityObserverFixedSuccess observer A i₀ = 0) ∨
      (¬ V13RealLinearParityObserverRhsParityMatchesTarget observer A i₀ ∧
        v13RealLinearParityObserverFixedSuccess observer A i₀ =
          (1 / 2 : Rat)) := by
  by_cases hmatch :
      V13RealLinearParityObserverRhsParityMatchesTarget observer A i₀
  · rcases v13_zmod2_cases
        (v13RealLinearParityObserverConstant observer A) with hconst | hconst
    · left
      have hdet :
          V13RealLinearParityObserverDeterminesTarget observer A i₀ :=
        (v13RealLinearParityObserver_determinesTarget_iff
          observer A i₀).2 ⟨hconst, hmatch⟩
      exact
        ⟨hdet,
          v13RealLinearParityObserver_fixedSuccess_eq_one_of_determinesTarget
            observer A i₀ hdet⟩
    · right
      left
      have hcomp :
          V13RealLinearParityObserverDeterminesTargetComplement observer A i₀ :=
        (v13RealLinearParityObserver_determinesTargetComplement_iff
          observer A i₀).2 ⟨hconst, hmatch⟩
      exact
        ⟨hcomp,
          v13RealLinearParityObserver_fixedSuccess_eq_zero_of_determinesTargetComplement
            observer A i₀ hcomp⟩
  · right
    right
    exact
      ⟨hmatch,
        v13RealLinearParityObserver_fixedSuccess_eq_half_of_not_rhsParityMatchesTarget
          observer A i₀ hmatch⟩

theorem v13RealLinearParityObserver_correct_card_eq_incorrect_card_of_not_blocked
    {m j : Nat} (observer : V13RealLinearParityObserver m j)
    (A : V13F2LinearEquiv m) (i₀ : Fin m)
    (hnot : ¬ V13RealLinearBitJuntaBlocked observer.toBitJunta A i₀) :
    Fintype.card
        (V13RealLinearBitJuntaFixedCorrect observer.toBitJunta A i₀) =
      Fintype.card
        (V13RealLinearBitJuntaFixedIncorrect observer.toBitJunta A i₀) :=
  v13RealLinearBitJunta_correct_card_eq_incorrect_card_of_not_blocked
    observer.toBitJunta A i₀ hnot

end Mettapedia.Computability.PNP
