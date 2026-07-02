import Mettapedia.Computability.PNP.V13RealRungOneLinear

/-!
# PNP v13 real rung one: row-observer hard core

This file does not assert the adaptive q-row probability bound.  It proves the
conditioned-fiber kernel-flip step needed by that theorem: for any fixed
certified linear map `A`, if the observed rows do not block a vector hitting
the target coordinate, then two worlds with opposite targets have the same
observed row transcript.

The remaining hard core is the span-counting statement that a q-row adaptive
observer hits the blocking event with probability at most about `2^(q-m)` under
the sampled invertible linear map.
-/

namespace Mettapedia.Computability.PNP

set_option autoImplicit false

lemma v13_zmod2_eq_one_of_ne_zero (a : ZMod 2) (h : a ≠ 0) : a = 1 := by
  fin_cases a
  · exact False.elim (h rfl)
  · rfl

lemma v13_zmod2_add_one_ne_self (a : ZMod 2) : a + 1 ≠ a := by
  fin_cases a <;> norm_num

/-- A single public row exposes the row functional of `A` and the matching RHS
bit. -/
abbrev V13RealLinearRowView (m : Nat) :=
  (F2Vec m → ZMod 2) × ZMod 2

def v13RealLinearRowView {m : Nat} (row : Fin m)
    (publicInput : V13RealLinearPublic m) : V13RealLinearRowView m :=
  (fun probe => publicInput.A.toEquiv probe row, publicInput.b row)

/-- Transcript seen by a non-adaptive observer after choosing a finite set of
rows.  Adaptive observers reduce to this object after fixing the branch. -/
def v13RealLinearRowsTranscript {m : Nat} (rows : Finset (Fin m))
    (publicInput : V13RealLinearPublic m) :
    ({row : Fin m // row ∈ rows} → V13RealLinearRowView m) :=
  fun row => v13RealLinearRowView row.1 publicInput

/-- The observed rows block the target when every vector in their common kernel
has zero target coordinate.  The q-row theorem needs a span-counting bound on
how often this blocking event occurs for sampled invertible `A`. -/
def V13RealLinearRowsBlockTarget {m : Nat}
    (A : V13F2LinearEquiv m) (rows : Finset (Fin m)) (i₀ : Fin m) : Prop :=
  ∀ w : F2Vec m,
    (∀ row : Fin m, row ∈ rows → A.toEquiv w row = 0) →
      w i₀ = 0

theorem v13RealLinear_exists_kernel_hit_of_not_rowsBlockTarget {m : Nat}
    {A : V13F2LinearEquiv m} {rows : Finset (Fin m)} {i₀ : Fin m}
    (hnot : ¬ V13RealLinearRowsBlockTarget A rows i₀) :
    ∃ w : F2Vec m,
      w i₀ = 1 ∧
        ∀ row : Fin m, row ∈ rows → A.toEquiv w row = 0 := by
  classical
  by_contra hexists
  apply hnot
  intro w hkernel
  by_contra hzero
  have hone : w i₀ = 1 :=
    v13_zmod2_eq_one_of_ne_zero (w i₀) hzero
  exact hexists ⟨w, hone, hkernel⟩

lemma v13RealLinear_same_rowView_after_kernel_add {m : Nat}
    (A : V13F2LinearEquiv m) (x w : F2Vec m) {row : Fin m}
    (hrow : A.toEquiv w row = 0) :
    v13RealLinearRowView row
        (v13RealLinearPublicInput
          ({ x := x, A := A } : V13RealLinearWorld m)) =
      v13RealLinearRowView row
        (v13RealLinearPublicInput
          ({ x := f2AddVec x w, A := A } : V13RealLinearWorld m)) := by
  apply Prod.ext
  · funext probe
    rfl
  · have hmap := congrFun (A.map_add x w) row
    simpa [v13RealLinearRowView, v13RealLinearPublicInput, f2AddVec, hrow]
      using hmap.symm

theorem v13RealLinear_same_rowsTranscript_after_kernel_add {m : Nat}
    (A : V13F2LinearEquiv m) (x w : F2Vec m) (rows : Finset (Fin m))
    (hkernel : ∀ row : Fin m, row ∈ rows → A.toEquiv w row = 0) :
    v13RealLinearRowsTranscript rows
        (v13RealLinearPublicInput
          ({ x := x, A := A } : V13RealLinearWorld m)) =
      v13RealLinearRowsTranscript rows
        (v13RealLinearPublicInput
          ({ x := f2AddVec x w, A := A } : V13RealLinearWorld m)) := by
  funext row
  exact
    v13RealLinear_same_rowView_after_kernel_add A x w
      (hkernel row.1 row.2)

theorem v13RealLinear_target_changes_after_kernel_hit {m : Nat}
    (A : V13F2LinearEquiv m) (x w : F2Vec m) {i₀ : Fin m}
    (hwi : w i₀ = 1) :
    v13RealLinearTarget i₀
        ({ x := f2AddVec x w, A := A } : V13RealLinearWorld m) ≠
      v13RealLinearTarget i₀
        ({ x := x, A := A } : V13RealLinearWorld m) := by
  intro hsame
  simp [v13RealLinearTarget, f2AddVec, hwi] at hsame

theorem v13RealLinear_opposite_targets_same_rowsTranscript_of_not_blocked
    {m : Nat} (A : V13F2LinearEquiv m) (rows : Finset (Fin m))
    (i₀ : Fin m) (hnot : ¬ V13RealLinearRowsBlockTarget A rows i₀) :
    ∃ omega₀ omega₁ : V13RealLinearWorld m,
      v13RealLinearRowsTranscript rows
          (v13RealLinearPublicInput omega₀) =
        v13RealLinearRowsTranscript rows
          (v13RealLinearPublicInput omega₁) ∧
      v13RealLinearTarget i₀ omega₀ ≠
        v13RealLinearTarget i₀ omega₁ := by
  rcases v13RealLinear_exists_kernel_hit_of_not_rowsBlockTarget
      (A := A) (rows := rows) (i₀ := i₀) hnot with
    ⟨w, hwi, hkernel⟩
  refine
    ⟨{ x := f2ZeroVec m, A := A },
      { x := f2AddVec (f2ZeroVec m) w, A := A },
      ?_, ?_⟩
  · exact
      v13RealLinear_same_rowsTranscript_after_kernel_add
        A (f2ZeroVec m) w rows hkernel
  · exact
      (v13RealLinear_target_changes_after_kernel_hit
        A (f2ZeroVec m) w hwi).symm

end Mettapedia.Computability.PNP
