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
            {A : V13RealLinearNoTargetRowsMap m i₀ //
              V13RealLinearNoTargetBitJuntaBlockedMap i₀ observer A} ≤
        4 * (2 ^ j) *
          Fintype.card (V13RealLinearNoTargetRowsMap m i₀)

def V13RealLinearNoTargetBitJuntaSuccessBound
    (m j : Nat) : Prop :=
  ∀ (i₀ : Fin m) (observer : V13RealLinearBitJuntaObserver m j),
    v13RealLinearNoTargetBitJuntaSuccess i₀ observer ≤
      (1 / 2 : Rat) + v13RealLinearBitJuntaEpsilon2 j m

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
