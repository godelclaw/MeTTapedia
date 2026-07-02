import Mettapedia.Computability.PNP.V13RealRungOneRowObservers

/-!
# PNP v13 real rung one: static row branches

Adaptive q-row observers reduce branch-by-branch to a fixed set of observed
rows.  This file proves the exact conditioned-fiber half theorem for one such
fixed branch: if the rows do not block the target coordinate, kernel flip gives
a bijection between correct and incorrect predictions over the hidden witness
space.
-/

namespace Mettapedia.Computability.PNP

set_option autoImplicit false

/-- A fixed branch of a row observer: it reads one row set and its decision
depends only on that row transcript. -/
structure V13RealLinearStaticRowObserver (m q : Nat) where
  rows : Finset (Fin m)
  decide : V13RealLinearWorld m → ZMod 2
  readBudget : rows.card ≤ q
  factorsThroughRows :
    ∀ omega₀ omega₁ : V13RealLinearWorld m,
      v13RealLinearRowsTranscript rows (v13RealLinearPublicInput omega₀) =
        v13RealLinearRowsTranscript rows (v13RealLinearPublicInput omega₁) →
      decide omega₀ = decide omega₁

def V13RealLinearFixedCorrect {m q : Nat}
    (observer : V13RealLinearStaticRowObserver m q)
    (A : V13F2LinearEquiv m) (i₀ : Fin m) :=
  {x : F2Vec m //
    observer.decide ({ x := x, A := A } : V13RealLinearWorld m) =
      v13RealLinearTarget i₀
        ({ x := x, A := A } : V13RealLinearWorld m)}

def V13RealLinearFixedIncorrect {m q : Nat}
    (observer : V13RealLinearStaticRowObserver m q)
    (A : V13F2LinearEquiv m) (i₀ : Fin m) :=
  {x : F2Vec m //
    observer.decide ({ x := x, A := A } : V13RealLinearWorld m) ≠
      v13RealLinearTarget i₀
        ({ x := x, A := A } : V13RealLinearWorld m)}

noncomputable instance {m q : Nat}
    (observer : V13RealLinearStaticRowObserver m q)
    (A : V13F2LinearEquiv m) (i₀ : Fin m) :
    Fintype (V13RealLinearFixedCorrect observer A i₀) := by
  classical
  unfold V13RealLinearFixedCorrect
  infer_instance

noncomputable instance {m q : Nat}
    (observer : V13RealLinearStaticRowObserver m q)
    (A : V13F2LinearEquiv m) (i₀ : Fin m) :
    Fintype (V13RealLinearFixedIncorrect observer A i₀) := by
  classical
  unfold V13RealLinearFixedIncorrect
  infer_instance

lemma v13_zmod2_eq_of_ne_left {a b c : ZMod 2}
    (hbc : c ≠ b) (hab : a ≠ b) : a = c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp at hbc hab ⊢

lemma v13RealLinear_staticRows_decide_same_after_kernel_add {m q : Nat}
    (observer : V13RealLinearStaticRowObserver m q)
    (A : V13F2LinearEquiv m) (x w : F2Vec m)
    (hkernel :
      ∀ row : Fin m, row ∈ observer.rows → A.toEquiv w row = 0) :
    observer.decide ({ x := x, A := A } : V13RealLinearWorld m) =
      observer.decide
        ({ x := f2AddVec x w, A := A } : V13RealLinearWorld m) := by
  exact
    observer.factorsThroughRows
      ({ x := x, A := A } : V13RealLinearWorld m)
      ({ x := f2AddVec x w, A := A } : V13RealLinearWorld m)
      (v13RealLinear_same_rowsTranscript_after_kernel_add
        A x w observer.rows hkernel)

def v13RealLinear_staticRows_correctIncorrectEquiv {m q : Nat}
    (observer : V13RealLinearStaticRowObserver m q)
    (A : V13F2LinearEquiv m) (i₀ : Fin m)
    (w : F2Vec m) (hwi : w i₀ = 1)
    (hkernel :
      ∀ row : Fin m, row ∈ observer.rows → A.toEquiv w row = 0) :
    V13RealLinearFixedCorrect observer A i₀ ≃
      V13RealLinearFixedIncorrect observer A i₀ where
  toFun x :=
    ⟨f2AddVec x.val w, by
      have hdec :=
        v13RealLinear_staticRows_decide_same_after_kernel_add
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
            ({ x := f2AddVec x.val w, A := A } :
              V13RealLinearWorld m) := hbad.symm
        _ = observer.decide
            ({ x := x.val, A := A } : V13RealLinearWorld m) := hdec.symm
        _ = v13RealLinearTarget i₀
            ({ x := x.val, A := A } : V13RealLinearWorld m) := x.property⟩
  invFun x :=
    ⟨f2AddVec x.val w, by
      have hdec :=
        v13RealLinear_staticRows_decide_same_after_kernel_add
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
              ({ x := f2AddVec x.val w, A := A } :
                V13RealLinearWorld m) =
            observer.decide
              ({ x := x.val, A := A } : V13RealLinearWorld m) :=
        hdec.symm
      have hdecFlip_ne_targetOrig :
          observer.decide
              ({ x := f2AddVec x.val w, A := A } :
                V13RealLinearWorld m) ≠
            v13RealLinearTarget i₀
              ({ x := x.val, A := A } : V13RealLinearWorld m) := by
        intro hbad
        exact x.property (hdecFlipped.symm.trans hbad)
      exact
        v13_zmod2_eq_of_ne_left htargetNe hdecFlip_ne_targetOrig⟩
  left_inv x := by
    apply Subtype.ext
    funext j
    exact f2_add_right_self (x.val j) (w j)
  right_inv x := by
    apply Subtype.ext
    funext j
    exact f2_add_right_self (x.val j) (w j)

theorem v13RealLinear_staticRows_correct_card_eq_incorrect_card_of_kernel_hit
    {m q : Nat} (observer : V13RealLinearStaticRowObserver m q)
    (A : V13F2LinearEquiv m) (i₀ : Fin m)
    (w : F2Vec m) (hwi : w i₀ = 1)
    (hkernel :
      ∀ row : Fin m, row ∈ observer.rows → A.toEquiv w row = 0) :
    Fintype.card (V13RealLinearFixedCorrect observer A i₀) =
      Fintype.card (V13RealLinearFixedIncorrect observer A i₀) :=
  Fintype.card_congr
    (v13RealLinear_staticRows_correctIncorrectEquiv
      observer A i₀ w hwi hkernel)

theorem v13RealLinear_staticRows_correct_card_eq_incorrect_card_of_not_blocked
    {m q : Nat} (observer : V13RealLinearStaticRowObserver m q)
    (A : V13F2LinearEquiv m) (i₀ : Fin m)
    (hnot : ¬ V13RealLinearRowsBlockTarget A observer.rows i₀) :
    Fintype.card (V13RealLinearFixedCorrect observer A i₀) =
      Fintype.card (V13RealLinearFixedIncorrect observer A i₀) := by
  rcases v13RealLinear_exists_kernel_hit_of_not_rowsBlockTarget
      (A := A) (rows := observer.rows) (i₀ := i₀) hnot with
    ⟨w, hwi, hkernel⟩
  exact
    v13RealLinear_staticRows_correct_card_eq_incorrect_card_of_kernel_hit
      observer A i₀ w hwi hkernel

end Mettapedia.Computability.PNP
