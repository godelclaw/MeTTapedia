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
