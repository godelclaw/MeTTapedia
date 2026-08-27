import Mettapedia.Computability.PNP.V13RealRungOneStaticRows

/-!
# PNP v13 real rung one: adaptive row branches

This module lifts the fixed-branch kernel-flip theorem to an adaptive branch
interface.  A branch is stable when adding a vector in the kernel of the rows
read by that branch keeps the observer on the same branch.  Under that
stability condition, every non-blocked branch has exactly paired correct and
incorrect hidden witnesses.

The remaining probabilistic theorem is now the row-span counting statement
that the realized branch is blocked with probability at most about `2^(q-m)`.
-/

namespace Mettapedia.Computability.PNP

set_option autoImplicit false

/-- Adaptive q-row observer represented by its realized branch.  Each branch
has a static row observer, and kernel moves invisible to that branch keep the
execution on the same branch. -/
structure V13RealLinearAdaptiveRowObserver (m q : Nat) where
  Branch : Type
  branch : V13RealLinearWorld m → Branch
  staticBranch : Branch → V13RealLinearStaticRowObserver m q
  decide : V13RealLinearWorld m → ZMod 2
  branchDecision :
    ∀ omega : V13RealLinearWorld m,
      decide omega = (staticBranch (branch omega)).decide omega
  branchStable :
    ∀ (A : V13F2LinearEquiv m) (x w : F2Vec m) (b : Branch),
      branch ({ x := x, A := A } : V13RealLinearWorld m) = b →
      (∀ row : Fin m, row ∈ (staticBranch b).rows →
        A.toEquiv w row = 0) →
      branch ({ x := f2AddVec x w, A := A } :
        V13RealLinearWorld m) = b

def V13RealLinearAdaptiveBranchCorrect {m q : Nat}
    (observer : V13RealLinearAdaptiveRowObserver m q)
    (A : V13F2LinearEquiv m) (i₀ : Fin m) (b : observer.Branch) :=
  {x : F2Vec m //
    observer.branch ({ x := x, A := A } : V13RealLinearWorld m) = b ∧
      observer.decide ({ x := x, A := A } : V13RealLinearWorld m) =
        v13RealLinearTarget i₀
          ({ x := x, A := A } : V13RealLinearWorld m)}

def V13RealLinearAdaptiveBranchIncorrect {m q : Nat}
    (observer : V13RealLinearAdaptiveRowObserver m q)
    (A : V13F2LinearEquiv m) (i₀ : Fin m) (b : observer.Branch) :=
  {x : F2Vec m //
    observer.branch ({ x := x, A := A } : V13RealLinearWorld m) = b ∧
      observer.decide ({ x := x, A := A } : V13RealLinearWorld m) ≠
        v13RealLinearTarget i₀
          ({ x := x, A := A } : V13RealLinearWorld m)}

noncomputable instance {m q : Nat}
    (observer : V13RealLinearAdaptiveRowObserver m q)
    (A : V13F2LinearEquiv m) (i₀ : Fin m) (b : observer.Branch) :
    Fintype (V13RealLinearAdaptiveBranchCorrect observer A i₀ b) := by
  classical
  unfold V13RealLinearAdaptiveBranchCorrect
  infer_instance

noncomputable instance {m q : Nat}
    (observer : V13RealLinearAdaptiveRowObserver m q)
    (A : V13F2LinearEquiv m) (i₀ : Fin m) (b : observer.Branch) :
    Fintype (V13RealLinearAdaptiveBranchIncorrect observer A i₀ b) := by
  classical
  unfold V13RealLinearAdaptiveBranchIncorrect
  infer_instance

lemma v13RealLinear_adaptive_decide_same_after_kernel_add_on_branch
    {m q : Nat} (observer : V13RealLinearAdaptiveRowObserver m q)
    (A : V13F2LinearEquiv m) (x w : F2Vec m) (b : observer.Branch)
    (hbranch :
      observer.branch ({ x := x, A := A } : V13RealLinearWorld m) = b)
    (hkernel :
      ∀ row : Fin m, row ∈ (observer.staticBranch b).rows →
        A.toEquiv w row = 0) :
    observer.decide ({ x := x, A := A } : V13RealLinearWorld m) =
      observer.decide
        ({ x := f2AddVec x w, A := A } : V13RealLinearWorld m) := by
  have hbranchFlip :=
    observer.branchStable A x w b hbranch hkernel
  calc
    observer.decide ({ x := x, A := A } : V13RealLinearWorld m) =
        (observer.staticBranch b).decide
          ({ x := x, A := A } : V13RealLinearWorld m) := by
          rw [observer.branchDecision, hbranch]
    _ =
        (observer.staticBranch b).decide
          ({ x := f2AddVec x w, A := A } :
            V13RealLinearWorld m) := by
          exact
            v13RealLinear_staticRows_decide_same_after_kernel_add
              (observer.staticBranch b) A x w hkernel
    _ =
        observer.decide
          ({ x := f2AddVec x w, A := A } :
            V13RealLinearWorld m) := by
          rw [observer.branchDecision, hbranchFlip]

def v13RealLinear_adaptiveBranch_correctIncorrectEquiv {m q : Nat}
    (observer : V13RealLinearAdaptiveRowObserver m q)
    (A : V13F2LinearEquiv m) (i₀ : Fin m) (b : observer.Branch)
    (w : F2Vec m) (hwi : w i₀ = 1)
    (hkernel :
      ∀ row : Fin m, row ∈ (observer.staticBranch b).rows →
        A.toEquiv w row = 0) :
    V13RealLinearAdaptiveBranchCorrect observer A i₀ b ≃
      V13RealLinearAdaptiveBranchIncorrect observer A i₀ b where
  toFun x :=
    ⟨f2AddVec x.val w, by
      have hbranchFlip :=
        observer.branchStable A x.val w b x.property.1 hkernel
      have hdec :=
        v13RealLinear_adaptive_decide_same_after_kernel_add_on_branch
          observer A x.val w b x.property.1 hkernel
      have htargetNe :
          v13RealLinearTarget i₀
              ({ x := f2AddVec x.val w, A := A } :
                V13RealLinearWorld m) ≠
            v13RealLinearTarget i₀
              ({ x := x.val, A := A } : V13RealLinearWorld m) :=
        v13RealLinear_target_changes_after_kernel_hit A x.val w hwi
      refine ⟨hbranchFlip, ?_⟩
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
            ({ x := x.val, A := A } : V13RealLinearWorld m) :=
              x.property.2⟩
  invFun x :=
    ⟨f2AddVec x.val w, by
      have hbranchFlip :=
        observer.branchStable A x.val w b x.property.1 hkernel
      have hdec :=
        v13RealLinear_adaptive_decide_same_after_kernel_add_on_branch
          observer A x.val w b x.property.1 hkernel
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
        exact x.property.2 (hdecFlipped.symm.trans hbad)
      exact
        ⟨hbranchFlip,
          v13_zmod2_eq_of_ne_left htargetNe hdecFlip_ne_targetOrig⟩⟩
  left_inv x := by
    apply Subtype.ext
    funext j
    exact f2_add_right_self (x.val j) (w j)
  right_inv x := by
    apply Subtype.ext
    funext j
    exact f2_add_right_self (x.val j) (w j)

theorem v13RealLinear_adaptiveBranch_correct_card_eq_incorrect_card_of_kernel_hit
    {m q : Nat} (observer : V13RealLinearAdaptiveRowObserver m q)
    (A : V13F2LinearEquiv m) (i₀ : Fin m) (b : observer.Branch)
    (w : F2Vec m) (hwi : w i₀ = 1)
    (hkernel :
      ∀ row : Fin m, row ∈ (observer.staticBranch b).rows →
        A.toEquiv w row = 0) :
    Fintype.card (V13RealLinearAdaptiveBranchCorrect observer A i₀ b) =
      Fintype.card
        (V13RealLinearAdaptiveBranchIncorrect observer A i₀ b) :=
  Fintype.card_congr
    (v13RealLinear_adaptiveBranch_correctIncorrectEquiv
      observer A i₀ b w hwi hkernel)

theorem v13RealLinear_adaptiveBranch_correct_card_eq_incorrect_card_of_not_blocked
    {m q : Nat} (observer : V13RealLinearAdaptiveRowObserver m q)
    (A : V13F2LinearEquiv m) (i₀ : Fin m) (b : observer.Branch)
    (hnot :
      ¬ V13RealLinearRowsBlockTarget
          A (observer.staticBranch b).rows i₀) :
    Fintype.card (V13RealLinearAdaptiveBranchCorrect observer A i₀ b) =
      Fintype.card
        (V13RealLinearAdaptiveBranchIncorrect observer A i₀ b) := by
  rcases v13RealLinear_exists_kernel_hit_of_not_rowsBlockTarget
      (A := A) (rows := (observer.staticBranch b).rows) (i₀ := i₀)
      hnot with
    ⟨w, hwi, hkernel⟩
  exact
    v13RealLinear_adaptiveBranch_correct_card_eq_incorrect_card_of_kernel_hit
      observer A i₀ b w hwi hkernel

end Mettapedia.Computability.PNP
