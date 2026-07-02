import Mettapedia.Computability.PNP.V13RealRungOneAdaptiveRows
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# PNP v13 real rung one: q-row bound assembly

This file packages the finite sampled experiment for the real row-observer
theorem.  The central public wrapper uses the uniform sampler over all
certified invertible maps.  Its only remaining pinned counting obligation is
`V13RealLinearUniformInvertibleRowSpanCountingBound`.
-/

namespace Mettapedia.Computability.PNP

set_option autoImplicit false

/-- A finite experiment samples an invertible linear map from `Seed` and then
the hidden witness vector uniformly. -/
structure V13RealLinearAdaptiveQRowExperiment
    (m q : Nat) (Seed : Type*) where
  sampleA : Seed → V13F2LinearEquiv m
  observer : V13RealLinearAdaptiveRowObserver m q

/-- The certified invertible maps are finite because they are equivalences of
the finite vector space with proof fields attached. -/
noncomputable instance v13F2LinearEquivFintype (m : Nat) :
    Fintype (V13F2LinearEquiv m) := by
  classical
  let Certified :=
    {e : F2Vec m ≃ F2Vec m //
      (∀ x y : F2Vec m,
        e (f2AddVec x y) = f2AddVec (e x) (e y)) ∧
          e (f2ZeroVec m) = f2ZeroVec m}
  haveI : Fintype Certified := by
    infer_instance
  exact
    Fintype.ofEquiv Certified
      { toFun := fun e =>
          { toEquiv := e.val
            map_add := e.property.1
            map_zero := e.property.2 }
        invFun := fun A =>
          ⟨A.toEquiv, A.map_add, A.map_zero⟩
        left_inv := by
          intro e
          apply Subtype.ext
          rfl
        right_inv := by
          intro A
          cases A
          rfl }

def v13RealLinearUniformQRowExperiment {m q : Nat}
    (observer : V13RealLinearAdaptiveRowObserver m q) :
    V13RealLinearAdaptiveQRowExperiment m q (V13F2LinearEquiv m) where
  sampleA := id
  observer := observer

abbrev V13RealLinearAdaptiveQRowWorld (m : Nat) (Seed : Type*) :=
  Seed × F2Vec m

def V13RealLinearAdaptiveQRowExperiment.world {m q : Nat} {Seed : Type*}
    (E : V13RealLinearAdaptiveQRowExperiment m q Seed)
    (omega : V13RealLinearAdaptiveQRowWorld m Seed) :
    V13RealLinearWorld m :=
  { x := omega.2, A := E.sampleA omega.1 }

def V13RealLinearAdaptiveQRowExperiment.target {m q : Nat} {Seed : Type*}
    (E : V13RealLinearAdaptiveQRowExperiment m q Seed) (i₀ : Fin m)
    (omega : V13RealLinearAdaptiveQRowWorld m Seed) : ZMod 2 :=
  v13RealLinearTarget i₀ (E.world omega)

def V13RealLinearAdaptiveQRowExperiment.decision {m q : Nat} {Seed : Type*}
    (E : V13RealLinearAdaptiveQRowExperiment m q Seed)
    (omega : V13RealLinearAdaptiveQRowWorld m Seed) : ZMod 2 :=
  E.observer.decide (E.world omega)

def V13RealLinearAdaptiveQRowExperiment.branch {m q : Nat} {Seed : Type*}
    (E : V13RealLinearAdaptiveQRowExperiment m q Seed)
    (omega : V13RealLinearAdaptiveQRowWorld m Seed) : E.observer.Branch :=
  E.observer.branch (E.world omega)

def V13RealLinearAdaptiveQRowExperiment.branchRows {m q : Nat}
    {Seed : Type*} (E : V13RealLinearAdaptiveQRowExperiment m q Seed)
    (omega : V13RealLinearAdaptiveQRowWorld m Seed) : Finset (Fin m) :=
  (E.observer.staticBranch (E.branch omega)).rows

theorem V13RealLinearAdaptiveQRowExperiment.branchRows_card_le {m q : Nat}
    {Seed : Type*} (E : V13RealLinearAdaptiveQRowExperiment m q Seed)
    (omega : V13RealLinearAdaptiveQRowWorld m Seed) :
    (E.branchRows omega).card ≤ q := by
  exact (E.observer.staticBranch (E.branch omega)).readBudget

def V13RealLinearAdaptiveQRowExperiment.blocked {m q : Nat} {Seed : Type*}
    (E : V13RealLinearAdaptiveQRowExperiment m q Seed) (i₀ : Fin m)
    (omega : V13RealLinearAdaptiveQRowWorld m Seed) : Prop :=
  V13RealLinearRowsBlockTarget
    (E.sampleA omega.1) (E.branchRows omega) i₀

/-- A coefficient assignment for the span of a finite set of public rows. -/
abbrev V13RealLinearRowCombination {m : Nat} (rows : Finset (Fin m)) :=
  {row : Fin m // row ∈ rows} → ZMod 2

def v13RealLinearRowCombinationEval {m : Nat}
    (A : V13F2LinearEquiv m) (rows : Finset (Fin m))
    (coeff : V13RealLinearRowCombination rows) (w : F2Vec m) : ZMod 2 :=
  Finset.univ.sum
    (fun row : {row : Fin m // row ∈ rows} =>
      coeff row * A.toEquiv w row.1)

def V13RealLinearRowsGenerateTarget {m : Nat}
    (A : V13F2LinearEquiv m) (rows : Finset (Fin m)) (i₀ : Fin m) :
    Prop :=
  ∃ coeff : V13RealLinearRowCombination rows,
    ∀ w : F2Vec m,
      v13RealLinearRowCombinationEval A rows coeff w = w i₀

theorem v13RealLinear_not_rowsGenerateTarget_of_rows_card_zero {m : Nat}
    (A : V13F2LinearEquiv m) {rows : Finset (Fin m)} (i₀ : Fin m)
    (hrows : rows.card = 0) :
    ¬ V13RealLinearRowsGenerateTarget A rows i₀ := by
  classical
  intro hgen
  rcases hgen with ⟨coeff, hcoeff⟩
  have hrowsEmpty : rows = ∅ := Finset.card_eq_zero.mp hrows
  subst rows
  have htarget := hcoeff (v13RealLinearSingleBit i₀)
  norm_num [v13RealLinearRowCombinationEval,
    v13RealLinearSingleBit] at htarget

def V13RealLinearAdaptiveQRowExperiment.generated {m q : Nat}
    {Seed : Type*} (E : V13RealLinearAdaptiveQRowExperiment m q Seed)
    (i₀ : Fin m) (omega : V13RealLinearAdaptiveQRowWorld m Seed) : Prop :=
  V13RealLinearRowsGenerateTarget
    (E.sampleA omega.1) (E.branchRows omega) i₀

def v13RealLinearRowFunctional {m : Nat}
    (A : V13F2LinearEquiv m) (row : Fin m) :
    F2Vec m →ₗ[ZMod 2] ZMod 2 :=
  (AddMonoidHom.toZModLinearMap 2
    { toFun := fun w : F2Vec m => A.toEquiv w row
      map_zero' := by
        change A.toEquiv (0 : F2Vec m) row = 0
        have hzero : (0 : F2Vec m) = f2ZeroVec m := by
          funext j
          rfl
        rw [hzero]
        exact congrFun A.map_zero row
      map_add' := by
        intro x y
        exact congrFun (A.map_add x y) row })

def v13RealLinearTargetFunctional {m : Nat} (i₀ : Fin m) :
    F2Vec m →ₗ[ZMod 2] ZMod 2 :=
  LinearMap.proj i₀

theorem v13RealLinear_rowCombination_card {m : Nat}
    (rows : Finset (Fin m)) :
    Fintype.card (V13RealLinearRowCombination rows) = 2 ^ rows.card := by
  classical
  simp [V13RealLinearRowCombination]

theorem v13RealLinear_rowCombination_card_le_of_rows_card_le {m q : Nat}
    {rows : Finset (Fin m)} (hrows : rows.card ≤ q) :
    Fintype.card (V13RealLinearRowCombination rows) ≤ 2 ^ q := by
  classical
  rw [v13RealLinear_rowCombination_card rows]
  exact Nat.pow_le_pow_right (by norm_num : 0 < 2) hrows

theorem v13RealLinear_rowCombination_card_le_for_branch {m q : Nat}
    {Seed : Type*} (E : V13RealLinearAdaptiveQRowExperiment m q Seed)
    (omega : V13RealLinearAdaptiveQRowWorld m Seed) :
    Fintype.card (V13RealLinearRowCombination (E.branchRows omega)) ≤
      2 ^ q :=
  v13RealLinear_rowCombination_card_le_of_rows_card_le
    (E.branchRows_card_le omega)

theorem v13RealLinear_rowsBlockTarget_of_rowsGenerateTarget {m : Nat}
    (A : V13F2LinearEquiv m) (rows : Finset (Fin m)) (i₀ : Fin m)
    (hgen : V13RealLinearRowsGenerateTarget A rows i₀) :
    V13RealLinearRowsBlockTarget A rows i₀ := by
  rcases hgen with ⟨coeff, hcoeff⟩
  intro w hkernel
  have hsum :
      v13RealLinearRowCombinationEval A rows coeff w = 0 := by
    unfold v13RealLinearRowCombinationEval
    simp [hkernel]
  calc
    w i₀ = v13RealLinearRowCombinationEval A rows coeff w := (hcoeff w).symm
    _ = 0 := hsum

theorem v13RealLinear_rowsGenerateTarget_of_rowsBlockTarget {m : Nat}
    (A : V13F2LinearEquiv m) (rows : Finset (Fin m)) (i₀ : Fin m)
    (hblock : V13RealLinearRowsBlockTarget A rows i₀) :
    V13RealLinearRowsGenerateTarget A rows i₀ := by
  classical
  let rowFunctional : {row : Fin m // row ∈ rows} →
      F2Vec m →ₗ[ZMod 2] ZMod 2 :=
    fun row => v13RealLinearRowFunctional A row.1
  let targetFunctional : F2Vec m →ₗ[ZMod 2] ZMod 2 :=
    v13RealLinearTargetFunctional i₀
  have hker :
      ⨅ row, LinearMap.ker (rowFunctional row) ≤
        LinearMap.ker targetFunctional := by
    intro w hw
    have hzero : w i₀ = 0 := by
      apply hblock
      intro row hrow
      have hmem :
          w ∈ LinearMap.ker
              (rowFunctional (⟨row, hrow⟩ : {row : Fin m // row ∈ rows})) :=
        (Submodule.mem_iInf _).1 hw ⟨row, hrow⟩
      simpa [rowFunctional, v13RealLinearRowFunctional] using hmem
    simpa [targetFunctional, v13RealLinearTargetFunctional] using hzero
  have hspan :
      targetFunctional ∈
        Submodule.span (ZMod 2) (Set.range rowFunctional) :=
    mem_span_of_iInf_ker_le_ker hker
  rcases (Submodule.mem_span_range_iff_exists_fun (R := ZMod 2)).1
      hspan with
    ⟨coeff, hcoeff⟩
  refine ⟨coeff, ?_⟩
  intro w
  have happly := LinearMap.congr_fun hcoeff w
  simpa [v13RealLinearRowCombinationEval, rowFunctional,
    targetFunctional, v13RealLinearRowFunctional,
    v13RealLinearTargetFunctional] using happly

theorem v13RealLinear_rowsBlockTarget_iff_rowsGenerateTarget {m : Nat}
    (A : V13F2LinearEquiv m) (rows : Finset (Fin m)) (i₀ : Fin m) :
    V13RealLinearRowsBlockTarget A rows i₀ ↔
      V13RealLinearRowsGenerateTarget A rows i₀ :=
  ⟨v13RealLinear_rowsGenerateTarget_of_rowsBlockTarget A rows i₀,
    v13RealLinear_rowsBlockTarget_of_rowsGenerateTarget A rows i₀⟩

theorem v13RealLinear_rowsGenerateTarget_singleton_iff {m : Nat}
    (A : V13F2LinearEquiv m) (row i₀ : Fin m) :
    V13RealLinearRowsGenerateTarget A ({row} : Finset (Fin m)) i₀ ↔
      ∀ w : F2Vec m, A.toEquiv w row = w i₀ := by
  classical
  constructor
  · intro hgen
    rcases hgen with ⟨coeff, hcoeff⟩
    let c : ZMod 2 :=
      coeff (default : {r : Fin m // r ∈ ({row} : Finset (Fin m))})
    have hcoeffEval :
        ∀ w : F2Vec m, c * A.toEquiv w row = w i₀ := by
      intro w
      have h := hcoeff w
      simpa [v13RealLinearRowCombinationEval, c] using h
    have hc : c = 1 := by
      by_cases hc0 : c = 0
      · have htarget := hcoeffEval (v13RealLinearSingleBit i₀)
        simp [hc0, v13RealLinearSingleBit] at htarget
      · exact v13_zmod2_eq_one_of_ne_zero c hc0
    intro w
    have h := hcoeffEval w
    simpa [hc] using h
  · intro hrow
    refine ⟨fun _ => 1, ?_⟩
    intro w
    simp [v13RealLinearRowCombinationEval, hrow w]

/-- Rows whose public row functional is exactly the target coordinate. -/
noncomputable def V13RealLinearTargetRows {m : Nat}
    (A : V13F2LinearEquiv m) (i₀ : Fin m) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter
    (fun row : Fin m => ∀ w : F2Vec m, A.toEquiv w row = w i₀)

theorem v13RealLinear_mem_targetRows_iff {m : Nat}
    (A : V13F2LinearEquiv m) (i₀ row : Fin m) :
    row ∈ V13RealLinearTargetRows A i₀ ↔
      ∀ w : F2Vec m, A.toEquiv w row = w i₀ := by
  classical
  simp [V13RealLinearTargetRows]

theorem v13RealLinear_targetRows_card_le_one {m : Nat}
    (A : V13F2LinearEquiv m) (i₀ : Fin m) :
    (V13RealLinearTargetRows A i₀).card ≤ 1 := by
  classical
  rw [Finset.card_le_one_iff]
  intro row₀ row₁ hrow₀ hrow₁
  have htarget₀ :=
    (v13RealLinear_mem_targetRows_iff A i₀ row₀).1 hrow₀
  have htarget₁ :=
    (v13RealLinear_mem_targetRows_iff A i₀ row₁).1 hrow₁
  by_contra hne
  let w : F2Vec m := A.toEquiv.symm (v13RealLinearSingleBit row₀)
  have hsame : A.toEquiv w row₀ = A.toEquiv w row₁ := by
    rw [htarget₀ w, htarget₁ w]
  have hrow₀val : A.toEquiv w row₀ = 1 := by
    simp [w, v13RealLinearSingleBit]
  have hrow₁val : A.toEquiv w row₁ = 0 := by
    have hne₁₀ : row₁ ≠ row₀ := fun h => hne h.symm
    simp [w, v13RealLinearSingleBit, hne₁₀]
  rw [hrow₀val, hrow₁val] at hsame
  norm_num at hsame

def v13RealLinearSingleRowStaticObserver {m : Nat} (row : Fin m) :
    V13RealLinearStaticRowObserver m 1 where
  rows := {row}
  decide := fun omega => (v13RealLinearPublicInput omega).b row
  readBudget := by simp
  factorsThroughRows := by
    intro omega₀ omega₁ hsame
    have hrow :
        v13RealLinearRowView row (v13RealLinearPublicInput omega₀) =
          v13RealLinearRowView row (v13RealLinearPublicInput omega₁) :=
      congrFun hsame ⟨row, by simp⟩
    exact congrArg Prod.snd hrow

noncomputable def v13RealLinearTargetRowChoice {m : Nat}
    (A : V13F2LinearEquiv m) (i₀ : Fin m) : Fin m := by
  classical
  exact
    if h : (V13RealLinearTargetRows A i₀).Nonempty then
      h.choose
    else
      i₀

theorem v13RealLinearTargetRowChoice_mem_of_nonempty {m : Nat}
    (A : V13F2LinearEquiv m) (i₀ : Fin m)
    (h : (V13RealLinearTargetRows A i₀).Nonempty) :
    v13RealLinearTargetRowChoice A i₀ ∈ V13RealLinearTargetRows A i₀ := by
  classical
  unfold v13RealLinearTargetRowChoice
  simpa [h] using h.choose_spec

/-- The current adaptive-row interface permits choosing a target row from the
sampled map before the row read.  This observer exposes the exact counting
burden left in the `q = 1` low-positive case. -/
noncomputable def v13RealLinearTargetRowObserver {m : Nat} (i₀ : Fin m) :
    V13RealLinearAdaptiveRowObserver m 1 where
  Branch := Fin m
  branch := fun omega => v13RealLinearTargetRowChoice omega.A i₀
  staticBranch := fun row => v13RealLinearSingleRowStaticObserver row
  decide := fun omega =>
    (v13RealLinearSingleRowStaticObserver
      (v13RealLinearTargetRowChoice omega.A i₀)).decide omega
  branchDecision := by
    intro omega
    rfl
  branchStable := by
    intro A x w b hbranch _hkernel
    exact hbranch

theorem V13RealLinearAdaptiveQRowExperiment.blocked_iff_generated
    {m q : Nat} {Seed : Type*}
    (E : V13RealLinearAdaptiveQRowExperiment m q Seed) (i₀ : Fin m)
    (omega : V13RealLinearAdaptiveQRowWorld m Seed) :
    E.blocked i₀ omega ↔ E.generated i₀ omega := by
  simpa [V13RealLinearAdaptiveQRowExperiment.blocked,
    V13RealLinearAdaptiveQRowExperiment.generated] using
    v13RealLinear_rowsBlockTarget_iff_rowsGenerateTarget
      (E.sampleA omega.1) (E.branchRows omega) i₀

theorem V13RealLinearAdaptiveQRowExperiment.not_generated_of_branchRows_card_zero
    {m q : Nat} {Seed : Type*}
    (E : V13RealLinearAdaptiveQRowExperiment m q Seed) (i₀ : Fin m)
    (omega : V13RealLinearAdaptiveQRowWorld m Seed)
    (hrows : (E.branchRows omega).card = 0) :
    ¬ E.generated i₀ omega := by
  unfold V13RealLinearAdaptiveQRowExperiment.generated
  exact
    v13RealLinear_not_rowsGenerateTarget_of_rows_card_zero
      (E.sampleA omega.1) i₀ hrows

theorem V13RealLinearAdaptiveQRowExperiment.not_generated_of_zero_budget
    {m : Nat} {Seed : Type*}
    (E : V13RealLinearAdaptiveQRowExperiment m 0 Seed) (i₀ : Fin m)
    (omega : V13RealLinearAdaptiveQRowWorld m Seed) :
    ¬ E.generated i₀ omega := by
  have hrows : (E.branchRows omega).card = 0 :=
    Nat.eq_zero_of_le_zero (E.branchRows_card_le omega)
  exact E.not_generated_of_branchRows_card_zero i₀ omega hrows

theorem V13RealLinearAdaptiveQRowExperiment.generated_one_budget_exists_target_row
    {m : Nat} {Seed : Type*}
    (E : V13RealLinearAdaptiveQRowExperiment m 1 Seed) (i₀ : Fin m)
    (omega : V13RealLinearAdaptiveQRowWorld m Seed)
    (hgen : E.generated i₀ omega) :
    ∃ row : Fin m,
      row ∈ E.branchRows omega ∧
        ∀ w : F2Vec m, (E.sampleA omega.1).toEquiv w row = w i₀ := by
  classical
  have hcardLe : (E.branchRows omega).card ≤ 1 :=
    E.branchRows_card_le omega
  have hcardNe : (E.branchRows omega).card ≠ 0 := by
    intro hzero
    exact (E.not_generated_of_branchRows_card_zero i₀ omega hzero) hgen
  have hcard : (E.branchRows omega).card = 1 := by
    omega
  rcases Finset.card_eq_one.mp hcard with ⟨row, hrows⟩
  refine ⟨row, ?_, ?_⟩
  · simp [hrows]
  · have hsingleton :
        V13RealLinearRowsGenerateTarget
          (E.sampleA omega.1) ({row} : Finset (Fin m)) i₀ := by
      simpa [V13RealLinearAdaptiveQRowExperiment.generated, hrows] using hgen
    exact
      (v13RealLinear_rowsGenerateTarget_singleton_iff
        (E.sampleA omega.1) row i₀).1 hsingleton

theorem V13RealLinearAdaptiveQRowExperiment.targetRows_nonempty_of_generated_one_budget
    {m : Nat} {Seed : Type*}
    (E : V13RealLinearAdaptiveQRowExperiment m 1 Seed) (i₀ : Fin m)
    (omega : V13RealLinearAdaptiveQRowWorld m Seed)
    (hgen : E.generated i₀ omega) :
    (V13RealLinearTargetRows (E.sampleA omega.1) i₀).Nonempty := by
  rcases E.generated_one_budget_exists_target_row i₀ omega hgen with
    ⟨row, _hmem, htarget⟩
  exact
    ⟨row,
      (v13RealLinear_mem_targetRows_iff
        (E.sampleA omega.1) i₀ row).2 htarget⟩

theorem v13RealLinear_targetRowObserver_generated_of_targetRows_nonempty
    {m : Nat} (i₀ : Fin m) (A : V13F2LinearEquiv m) (x : F2Vec m)
    (h : (V13RealLinearTargetRows A i₀).Nonempty) :
    (v13RealLinearUniformQRowExperiment
      (v13RealLinearTargetRowObserver i₀)).generated i₀ (A, x) := by
  classical
  have hmem :=
    v13RealLinearTargetRowChoice_mem_of_nonempty A i₀ h
  have htarget :
      ∀ w : F2Vec m,
        A.toEquiv w (v13RealLinearTargetRowChoice A i₀) = w i₀ :=
    (v13RealLinear_mem_targetRows_iff
      A i₀ (v13RealLinearTargetRowChoice A i₀)).1 hmem
  change
    V13RealLinearRowsGenerateTarget A
      ({v13RealLinearTargetRowChoice A i₀} : Finset (Fin m)) i₀
  exact
    (v13RealLinear_rowsGenerateTarget_singleton_iff
      A (v13RealLinearTargetRowChoice A i₀) i₀).2 htarget

theorem v13RealLinear_targetRowObserver_generated_iff_targetRows_nonempty
    {m : Nat} (i₀ : Fin m) (A : V13F2LinearEquiv m) (x : F2Vec m) :
    (v13RealLinearUniformQRowExperiment
      (v13RealLinearTargetRowObserver i₀)).generated i₀ (A, x) ↔
      (V13RealLinearTargetRows A i₀).Nonempty := by
  constructor
  · intro hgen
    exact
      (v13RealLinearUniformQRowExperiment
        (v13RealLinearTargetRowObserver i₀)).targetRows_nonempty_of_generated_one_budget
          i₀ (A, x) hgen
  · intro hnonempty
    exact
      v13RealLinear_targetRowObserver_generated_of_targetRows_nonempty
        i₀ A x hnonempty

def V13RealLinearUniformTargetRowOccurrence {m : Nat} (i₀ : Fin m) :=
  {A : V13F2LinearEquiv m // (V13RealLinearTargetRows A i₀).Nonempty}

noncomputable instance {m : Nat} (i₀ : Fin m) :
    Fintype (V13RealLinearUniformTargetRowOccurrence i₀) := by
  classical
  unfold V13RealLinearUniformTargetRowOccurrence
  infer_instance

noncomputable def v13RealLinearUniformTargetRowOccurrenceMass {m : Nat}
    (i₀ : Fin m) : Rat :=
  (Fintype.card (V13RealLinearUniformTargetRowOccurrence i₀) : Rat) /
    (Fintype.card (V13F2LinearEquiv m) : Rat)

def V13RealLinearAdaptiveQRowExperiment.correct {m q : Nat} {Seed : Type*}
    (E : V13RealLinearAdaptiveQRowExperiment m q Seed) (i₀ : Fin m)
    (omega : V13RealLinearAdaptiveQRowWorld m Seed) : Prop :=
  E.decision omega = E.target i₀ omega

def V13RealLinearAdaptiveQRowCorrect {m q : Nat} {Seed : Type*}
    (E : V13RealLinearAdaptiveQRowExperiment m q Seed) (i₀ : Fin m) :=
  {omega : V13RealLinearAdaptiveQRowWorld m Seed // E.correct i₀ omega}

def V13RealLinearAdaptiveQRowBlocked {m q : Nat} {Seed : Type*}
    (E : V13RealLinearAdaptiveQRowExperiment m q Seed) (i₀ : Fin m) :=
  {omega : V13RealLinearAdaptiveQRowWorld m Seed // E.blocked i₀ omega}

def V13RealLinearAdaptiveQRowGenerated {m q : Nat} {Seed : Type*}
    (E : V13RealLinearAdaptiveQRowExperiment m q Seed) (i₀ : Fin m) :=
  {omega : V13RealLinearAdaptiveQRowWorld m Seed // E.generated i₀ omega}

def V13RealLinearAdaptiveQRowIncorrect {m q : Nat} {Seed : Type*}
    (E : V13RealLinearAdaptiveQRowExperiment m q Seed) (i₀ : Fin m) :=
  {omega : V13RealLinearAdaptiveQRowWorld m Seed // ¬ E.correct i₀ omega}

def V13RealLinearAdaptiveQRowUnblockedCorrect {m q : Nat} {Seed : Type*}
    (E : V13RealLinearAdaptiveQRowExperiment m q Seed) (i₀ : Fin m) :=
  {omega : V13RealLinearAdaptiveQRowWorld m Seed //
    E.correct i₀ omega ∧ ¬ E.blocked i₀ omega}

noncomputable instance {m q : Nat} {Seed : Type*} [Fintype Seed]
    (E : V13RealLinearAdaptiveQRowExperiment m q Seed) (i₀ : Fin m) :
    Fintype (V13RealLinearAdaptiveQRowCorrect E i₀) := by
  classical
  unfold V13RealLinearAdaptiveQRowCorrect
  infer_instance

noncomputable instance {m q : Nat} {Seed : Type*} [Fintype Seed]
    (E : V13RealLinearAdaptiveQRowExperiment m q Seed) (i₀ : Fin m) :
    Fintype (V13RealLinearAdaptiveQRowBlocked E i₀) := by
  classical
  unfold V13RealLinearAdaptiveQRowBlocked
  infer_instance

noncomputable instance {m q : Nat} {Seed : Type*} [Fintype Seed]
    (E : V13RealLinearAdaptiveQRowExperiment m q Seed) (i₀ : Fin m) :
    Fintype (V13RealLinearAdaptiveQRowGenerated E i₀) := by
  classical
  unfold V13RealLinearAdaptiveQRowGenerated
  infer_instance

noncomputable instance {m q : Nat} {Seed : Type*} [Fintype Seed]
    (E : V13RealLinearAdaptiveQRowExperiment m q Seed) (i₀ : Fin m) :
    Fintype (V13RealLinearAdaptiveQRowIncorrect E i₀) := by
  classical
  unfold V13RealLinearAdaptiveQRowIncorrect
  infer_instance

noncomputable instance {m q : Nat} {Seed : Type*} [Fintype Seed]
    (E : V13RealLinearAdaptiveQRowExperiment m q Seed) (i₀ : Fin m) :
    Fintype (V13RealLinearAdaptiveQRowUnblockedCorrect E i₀) := by
  classical
  unfold V13RealLinearAdaptiveQRowUnblockedCorrect
  infer_instance

noncomputable def v13RealLinear_targetRowObserverGeneratedEquivOccurrenceProd
    {m : Nat} (i₀ : Fin m) :
    V13RealLinearAdaptiveQRowGenerated
        (v13RealLinearUniformQRowExperiment
          (v13RealLinearTargetRowObserver i₀)) i₀ ≃
      V13RealLinearUniformTargetRowOccurrence i₀ × F2Vec m where
  toFun omega :=
    ⟨⟨omega.val.1,
        (v13RealLinear_targetRowObserver_generated_iff_targetRows_nonempty
          i₀ omega.val.1 omega.val.2).1 omega.property⟩,
      omega.val.2⟩
  invFun omega :=
    ⟨(omega.1.val, omega.2),
      (v13RealLinear_targetRowObserver_generated_iff_targetRows_nonempty
        i₀ omega.1.val omega.2).2 omega.1.property⟩
  left_inv omega := by
    rfl
  right_inv omega := by
    rfl

theorem v13RealLinear_targetRowObserverGenerated_card_eq
    {m : Nat} (i₀ : Fin m) :
    Fintype.card
        (V13RealLinearAdaptiveQRowGenerated
          (v13RealLinearUniformQRowExperiment
            (v13RealLinearTargetRowObserver i₀)) i₀) =
      Fintype.card (V13RealLinearUniformTargetRowOccurrence i₀) *
        Fintype.card (F2Vec m) := by
  classical
  rw [Fintype.card_congr
    (v13RealLinear_targetRowObserverGeneratedEquivOccurrenceProd i₀)]
  simp [Fintype.card_prod]

noncomputable def v13RealLinearAdaptiveQRowSuccess {m q : Nat}
    {Seed : Type*} [Fintype Seed]
    (E : V13RealLinearAdaptiveQRowExperiment m q Seed) (i₀ : Fin m) :
    Rat :=
  (Fintype.card (V13RealLinearAdaptiveQRowCorrect E i₀) : Rat) /
    (Fintype.card (V13RealLinearAdaptiveQRowWorld m Seed) : Rat)

noncomputable def v13RealLinearAdaptiveQRowBlockedMass {m q : Nat}
    {Seed : Type*} [Fintype Seed]
    (E : V13RealLinearAdaptiveQRowExperiment m q Seed) (i₀ : Fin m) :
    Rat :=
  (Fintype.card (V13RealLinearAdaptiveQRowBlocked E i₀) : Rat) /
    (Fintype.card (V13RealLinearAdaptiveQRowWorld m Seed) : Rat)

noncomputable def v13RealLinearAdaptiveQRowGeneratedMass {m q : Nat}
    {Seed : Type*} [Fintype Seed]
    (E : V13RealLinearAdaptiveQRowExperiment m q Seed) (i₀ : Fin m) :
    Rat :=
  (Fintype.card (V13RealLinearAdaptiveQRowGenerated E i₀) : Rat) /
    (Fintype.card (V13RealLinearAdaptiveQRowWorld m Seed) : Rat)

theorem v13RealLinear_targetRowObserverGeneratedMass_eq_occurrenceMass
    {m : Nat} (i₀ : Fin m) :
    v13RealLinearAdaptiveQRowGeneratedMass
        (v13RealLinearUniformQRowExperiment
          (v13RealLinearTargetRowObserver i₀)) i₀ =
      v13RealLinearUniformTargetRowOccurrenceMass i₀ := by
  classical
  unfold v13RealLinearAdaptiveQRowGeneratedMass
  unfold v13RealLinearUniformTargetRowOccurrenceMass
  rw [v13RealLinear_targetRowObserverGenerated_card_eq i₀]
  let O := Fintype.card (V13RealLinearUniformTargetRowOccurrence i₀)
  let A := Fintype.card (V13F2LinearEquiv m)
  let X := Fintype.card (F2Vec m)
  have hXposNat : 0 < X := by
    dsimp [X]
    exact Fintype.card_pos_iff.mpr ⟨f2ZeroVec m⟩
  have hXpos : (0 : Rat) < (X : Rat) := by
    exact_mod_cast hXposNat
  change ((Fintype.card (V13RealLinearUniformTargetRowOccurrence i₀) *
      Fintype.card (F2Vec m) : Nat) : Rat) /
      (Fintype.card (V13F2LinearEquiv m × F2Vec m) : Rat) =
    (Fintype.card (V13RealLinearUniformTargetRowOccurrence i₀) : Rat) /
      (Fintype.card (V13F2LinearEquiv m) : Rat)
  rw [Fintype.card_prod]
  change ((O * X : Nat) : Rat) / ((A * X : Nat) : Rat) =
    (O : Rat) / (A : Rat)
  rw [Nat.cast_mul, Nat.cast_mul]
  field_simp [hXpos.ne']

noncomputable def v13RealLinearAdaptiveQRowBlockedGeneratedEquiv
    {m q : Nat} {Seed : Type*}
    (E : V13RealLinearAdaptiveQRowExperiment m q Seed) (i₀ : Fin m) :
    V13RealLinearAdaptiveQRowBlocked E i₀ ≃
      V13RealLinearAdaptiveQRowGenerated E i₀ where
  toFun omega :=
    ⟨omega.val,
      (E.blocked_iff_generated i₀ omega.val).1 omega.property⟩
  invFun omega :=
    ⟨omega.val,
      (E.blocked_iff_generated i₀ omega.val).2 omega.property⟩
  left_inv omega := by
    rfl
  right_inv omega := by
    rfl

theorem v13RealLinearAdaptiveQRowBlockedMass_eq_generatedMass
    {m q : Nat} {Seed : Type*} [Fintype Seed]
    (E : V13RealLinearAdaptiveQRowExperiment m q Seed) (i₀ : Fin m) :
    v13RealLinearAdaptiveQRowBlockedMass E i₀ =
      v13RealLinearAdaptiveQRowGeneratedMass E i₀ := by
  unfold v13RealLinearAdaptiveQRowBlockedMass
  unfold v13RealLinearAdaptiveQRowGeneratedMass
  rw [Fintype.card_congr
    (v13RealLinearAdaptiveQRowBlockedGeneratedEquiv E i₀)]

theorem v13RealLinearAdaptiveQRowGenerated_card_eq_zero_of_zero_budget
    {m : Nat} {Seed : Type*} [Fintype Seed]
    (E : V13RealLinearAdaptiveQRowExperiment m 0 Seed) (i₀ : Fin m) :
    Fintype.card (V13RealLinearAdaptiveQRowGenerated E i₀) = 0 := by
  classical
  rw [Fintype.card_eq_zero_iff]
  exact
    ⟨fun omega =>
      E.not_generated_of_zero_budget i₀ omega.val omega.property⟩

theorem v13RealLinearAdaptiveQRowGeneratedMass_eq_zero_of_zero_budget
    {m : Nat} {Seed : Type*} [Fintype Seed]
    (E : V13RealLinearAdaptiveQRowExperiment m 0 Seed) (i₀ : Fin m) :
    v13RealLinearAdaptiveQRowGeneratedMass E i₀ = 0 := by
  unfold v13RealLinearAdaptiveQRowGeneratedMass
  rw [v13RealLinearAdaptiveQRowGenerated_card_eq_zero_of_zero_budget E i₀]
  simp

noncomputable def V13RealLinearAdaptiveQRowExperiment.branchFlipWitness
    {m q : Nat} {Seed : Type*}
    (E : V13RealLinearAdaptiveQRowExperiment m q Seed) (i₀ : Fin m)
    (seed : Seed) (b : E.observer.Branch) :
    F2Vec m := by
  classical
  exact
    if hnot :
      ¬ V13RealLinearRowsBlockTarget
          (E.sampleA seed) (E.observer.staticBranch b).rows i₀ then
      Classical.choose
        (v13RealLinear_exists_kernel_hit_of_not_rowsBlockTarget
          (A := E.sampleA seed) (rows := (E.observer.staticBranch b).rows)
          (i₀ := i₀) hnot)
    else
      f2ZeroVec m

lemma V13RealLinearAdaptiveQRowExperiment.branchFlipWitness_target
    {m q : Nat} {Seed : Type*}
    (E : V13RealLinearAdaptiveQRowExperiment m q Seed) (i₀ : Fin m)
    (seed : Seed) (b : E.observer.Branch)
    (hnot :
      ¬ V13RealLinearRowsBlockTarget
          (E.sampleA seed) (E.observer.staticBranch b).rows i₀) :
    E.branchFlipWitness i₀ seed b i₀ = 1 := by
  unfold V13RealLinearAdaptiveQRowExperiment.branchFlipWitness
  classical
  simpa [hnot] using
    (Classical.choose_spec
      (v13RealLinear_exists_kernel_hit_of_not_rowsBlockTarget
        (A := E.sampleA seed) (rows := (E.observer.staticBranch b).rows)
        (i₀ := i₀) hnot)).1

lemma V13RealLinearAdaptiveQRowExperiment.branchFlipWitness_kernel
    {m q : Nat} {Seed : Type*}
    (E : V13RealLinearAdaptiveQRowExperiment m q Seed) (i₀ : Fin m)
    (seed : Seed) (b : E.observer.Branch)
    (hnot :
      ¬ V13RealLinearRowsBlockTarget
          (E.sampleA seed) (E.observer.staticBranch b).rows i₀) :
    ∀ row : Fin m, row ∈ (E.observer.staticBranch b).rows →
      (E.sampleA seed).toEquiv
          (E.branchFlipWitness i₀ seed b) row = 0 := by
  unfold V13RealLinearAdaptiveQRowExperiment.branchFlipWitness
  classical
  simpa [hnot] using
    (Classical.choose_spec
      (v13RealLinear_exists_kernel_hit_of_not_rowsBlockTarget
        (A := E.sampleA seed) (rows := (E.observer.staticBranch b).rows)
        (i₀ := i₀) hnot)).2

noncomputable def v13RealLinearAdaptiveQRowUnblockedCorrectToIncorrect
    {m q : Nat} {Seed : Type*}
    (E : V13RealLinearAdaptiveQRowExperiment m q Seed) (i₀ : Fin m) :
    V13RealLinearAdaptiveQRowUnblockedCorrect E i₀ ↪
      V13RealLinearAdaptiveQRowIncorrect E i₀ where
  toFun omega :=
    let seed := omega.val.1
    let b := E.branch omega.val
    let hnot :
        ¬ V13RealLinearRowsBlockTarget
            (E.sampleA seed) (E.observer.staticBranch b).rows i₀ := by
      simpa [V13RealLinearAdaptiveQRowExperiment.blocked,
        V13RealLinearAdaptiveQRowExperiment.branchRows,
        V13RealLinearAdaptiveQRowExperiment.branch, seed, b]
        using omega.property.2
    let w := E.branchFlipWitness i₀ seed b
    ⟨(seed, f2AddVec omega.val.2 w), by
      dsimp [V13RealLinearAdaptiveQRowExperiment.correct,
        V13RealLinearAdaptiveQRowExperiment.decision,
        V13RealLinearAdaptiveQRowExperiment.target,
        V13RealLinearAdaptiveQRowExperiment.world]
      intro hbad
      have hkernel :
          ∀ row : Fin m, row ∈ (E.observer.staticBranch b).rows →
            (E.sampleA seed).toEquiv w row = 0 :=
        E.branchFlipWitness_kernel i₀ seed b hnot
      have hdecSame :
          E.observer.decide
              ({ x := omega.val.2, A := E.sampleA seed } :
                V13RealLinearWorld m) =
            E.observer.decide
              ({ x := f2AddVec omega.val.2 w, A := E.sampleA seed } :
                V13RealLinearWorld m) :=
        v13RealLinear_adaptive_decide_same_after_kernel_add_on_branch
          E.observer (E.sampleA seed) omega.val.2 w b (by
            simp [V13RealLinearAdaptiveQRowExperiment.branch,
              V13RealLinearAdaptiveQRowExperiment.world, b, seed])
          hkernel
      have htargetNe :
          v13RealLinearTarget i₀
              ({ x := f2AddVec omega.val.2 w, A := E.sampleA seed } :
                V13RealLinearWorld m) ≠
            v13RealLinearTarget i₀
              ({ x := omega.val.2, A := E.sampleA seed } :
                V13RealLinearWorld m) :=
        v13RealLinear_target_changes_after_kernel_hit
          (E.sampleA seed) omega.val.2 w
          (E.branchFlipWitness_target i₀ seed b hnot)
      apply htargetNe
      calc
        v13RealLinearTarget i₀
            ({ x := f2AddVec omega.val.2 w, A := E.sampleA seed } :
              V13RealLinearWorld m) =
          E.observer.decide
            ({ x := f2AddVec omega.val.2 w, A := E.sampleA seed } :
              V13RealLinearWorld m) := hbad.symm
        _ = E.observer.decide
            ({ x := omega.val.2, A := E.sampleA seed } :
              V13RealLinearWorld m) := hdecSame.symm
        _ = v13RealLinearTarget i₀
            ({ x := omega.val.2, A := E.sampleA seed } :
              V13RealLinearWorld m) := omega.property.1⟩
  inj' := by
    intro omega₀ omega₁ hmap
    apply Subtype.ext
    let seed₀ := omega₀.val.1
    let seed₁ := omega₁.val.1
    let b₀ := E.branch omega₀.val
    let b₁ := E.branch omega₁.val
    let hnot₀ :
        ¬ V13RealLinearRowsBlockTarget
            (E.sampleA seed₀) (E.observer.staticBranch b₀).rows i₀ := by
      simpa [V13RealLinearAdaptiveQRowExperiment.blocked,
        V13RealLinearAdaptiveQRowExperiment.branchRows,
        V13RealLinearAdaptiveQRowExperiment.branch, seed₀, b₀]
        using omega₀.property.2
    let hnot₁ :
        ¬ V13RealLinearRowsBlockTarget
            (E.sampleA seed₁) (E.observer.staticBranch b₁).rows i₀ := by
      simpa [V13RealLinearAdaptiveQRowExperiment.blocked,
        V13RealLinearAdaptiveQRowExperiment.branchRows,
        V13RealLinearAdaptiveQRowExperiment.branch, seed₁, b₁]
        using omega₁.property.2
    let w₀ := E.branchFlipWitness i₀ seed₀ b₀
    let w₁ := E.branchFlipWitness i₀ seed₁ b₁
    have hpair :
        (seed₀, f2AddVec omega₀.val.2 w₀) =
          (seed₁, f2AddVec omega₁.val.2 w₁) := by
      exact congrArg Subtype.val hmap
    have hseed : seed₀ = seed₁ := by
      injection hpair
    have hxflip : f2AddVec omega₀.val.2 w₀ =
        f2AddVec omega₁.val.2 w₁ := by
      injection hpair
    have hkernel₀ :
        ∀ row : Fin m, row ∈ (E.observer.staticBranch b₀).rows →
          (E.sampleA seed₀).toEquiv w₀ row = 0 :=
      E.branchFlipWitness_kernel i₀ seed₀ b₀ hnot₀
    have hkernel₁ :
        ∀ row : Fin m, row ∈ (E.observer.staticBranch b₁).rows →
          (E.sampleA seed₁).toEquiv w₁ row = 0 :=
      E.branchFlipWitness_kernel i₀ seed₁ b₁ hnot₁
    have hbranchFlip₀ :
        E.observer.branch
            ({ x := f2AddVec omega₀.val.2 w₀, A := E.sampleA seed₀ } :
              V13RealLinearWorld m) = b₀ :=
      E.observer.branchStable (E.sampleA seed₀) omega₀.val.2 w₀ b₀
        (by simp [V13RealLinearAdaptiveQRowExperiment.branch,
          V13RealLinearAdaptiveQRowExperiment.world, b₀, seed₀])
        hkernel₀
    have hbranchFlip₁ :
        E.observer.branch
            ({ x := f2AddVec omega₁.val.2 w₁, A := E.sampleA seed₁ } :
              V13RealLinearWorld m) = b₁ :=
      E.observer.branchStable (E.sampleA seed₁) omega₁.val.2 w₁ b₁
        (by simp [V13RealLinearAdaptiveQRowExperiment.branch,
          V13RealLinearAdaptiveQRowExperiment.world, b₁, seed₁])
        hkernel₁
    have hbranchEq : b₀ = b₁ := by
      calc
        b₀ =
            E.observer.branch
              ({ x := f2AddVec omega₀.val.2 w₀, A := E.sampleA seed₀ } :
                V13RealLinearWorld m) := hbranchFlip₀.symm
        _ =
            E.observer.branch
              ({ x := f2AddVec omega₁.val.2 w₁, A := E.sampleA seed₁ } :
                V13RealLinearWorld m) := by
              rw [hseed, hxflip]
        _ = b₁ := hbranchFlip₁
    have hw : w₀ = w₁ := by
      simp [w₀, w₁, hseed, hbranchEq]
    apply Prod.ext
    · exact hseed
    · funext j
      have hxpoint := congrFun hxflip j
      rw [hw] at hxpoint
      simp [f2AddVec] at hxpoint ⊢
      calc
        omega₀.val.2 j = omega₀.val.2 j + w₁ j + w₁ j := by
          rw [f2_add_right_self]
        _ = omega₁.val.2 j + w₁ j + w₁ j := by
          rw [hxpoint]
        _ = omega₁.val.2 j := by
          rw [f2_add_right_self]

noncomputable def v13RealLinearAdaptiveQRowCorrectToUnblockedOrBlocked
    {m q : Nat} {Seed : Type*}
    (E : V13RealLinearAdaptiveQRowExperiment m q Seed) (i₀ : Fin m) :
    V13RealLinearAdaptiveQRowCorrect E i₀ ↪
      V13RealLinearAdaptiveQRowUnblockedCorrect E i₀ ⊕
        V13RealLinearAdaptiveQRowBlocked E i₀ where
  toFun omega := by
    classical
    by_cases hblocked : E.blocked i₀ omega.val
    · exact Sum.inr ⟨omega.val, hblocked⟩
    · exact Sum.inl ⟨omega.val, omega.property, hblocked⟩
  inj' := by
    intro omega₀ omega₁ hmap
    classical
    by_cases hblocked₀ : E.blocked i₀ omega₀.val <;>
      by_cases hblocked₁ : E.blocked i₀ omega₁.val <;>
      simp [hblocked₀, hblocked₁] at hmap
    · exact
        Subtype.ext
          (congrArg
            (fun omega : V13RealLinearAdaptiveQRowBlocked E i₀ =>
              omega.val)
            hmap)
    · exact
        Subtype.ext
          (congrArg
            (fun omega : V13RealLinearAdaptiveQRowUnblockedCorrect E i₀ =>
              omega.val)
            hmap)

noncomputable def v13RealLinearAdaptiveQRowWorldCorrectIncorrectEquiv
    {m q : Nat} {Seed : Type*}
    (E : V13RealLinearAdaptiveQRowExperiment m q Seed) (i₀ : Fin m) :
    V13RealLinearAdaptiveQRowWorld m Seed ≃
      V13RealLinearAdaptiveQRowCorrect E i₀ ⊕
        V13RealLinearAdaptiveQRowIncorrect E i₀ where
  toFun omega := by
    classical
    by_cases hcorrect : E.correct i₀ omega
    · exact Sum.inl ⟨omega, hcorrect⟩
    · exact Sum.inr ⟨omega, hcorrect⟩
  invFun y :=
    Sum.elim
      (fun omega : V13RealLinearAdaptiveQRowCorrect E i₀ => omega.val)
      (fun omega : V13RealLinearAdaptiveQRowIncorrect E i₀ => omega.val)
      y
  left_inv omega := by
    classical
    by_cases hcorrect : E.correct i₀ omega <;> simp [hcorrect]
  right_inv y := by
    classical
    cases y with
    | inl omega =>
        change
          (if hcorrect : E.correct i₀ omega.val then
              Sum.inl
                (⟨omega.val, hcorrect⟩ :
                  V13RealLinearAdaptiveQRowCorrect E i₀)
            else
              Sum.inr
                (⟨omega.val, hcorrect⟩ :
                  V13RealLinearAdaptiveQRowIncorrect E i₀)) =
            Sum.inl omega
        rw [dif_pos omega.property]
        rfl
    | inr omega =>
        change
          (if hcorrect : E.correct i₀ omega.val then
              Sum.inl
                (⟨omega.val, hcorrect⟩ :
                  V13RealLinearAdaptiveQRowCorrect E i₀)
            else
              Sum.inr
                (⟨omega.val, hcorrect⟩ :
                  V13RealLinearAdaptiveQRowIncorrect E i₀)) =
            Sum.inr omega
        rw [dif_neg omega.property]
        rfl

theorem v13RealLinearAdaptiveQRow_unblockedCorrect_card_le_incorrect
    {m q : Nat} {Seed : Type*} [Fintype Seed]
    (E : V13RealLinearAdaptiveQRowExperiment m q Seed) (i₀ : Fin m) :
    Fintype.card (V13RealLinearAdaptiveQRowUnblockedCorrect E i₀) ≤
      Fintype.card (V13RealLinearAdaptiveQRowIncorrect E i₀) :=
  Fintype.card_le_of_embedding
    (v13RealLinearAdaptiveQRowUnblockedCorrectToIncorrect E i₀)

theorem v13RealLinearAdaptiveQRow_correct_card_le_incorrect_add_blocked
    {m q : Nat} {Seed : Type*} [Fintype Seed]
    (E : V13RealLinearAdaptiveQRowExperiment m q Seed) (i₀ : Fin m) :
    Fintype.card (V13RealLinearAdaptiveQRowCorrect E i₀) ≤
      Fintype.card (V13RealLinearAdaptiveQRowIncorrect E i₀) +
        Fintype.card (V13RealLinearAdaptiveQRowBlocked E i₀) := by
  have hsplit :
      Fintype.card (V13RealLinearAdaptiveQRowCorrect E i₀) ≤
        Fintype.card
          (V13RealLinearAdaptiveQRowUnblockedCorrect E i₀ ⊕
            V13RealLinearAdaptiveQRowBlocked E i₀) :=
    Fintype.card_le_of_embedding
      (v13RealLinearAdaptiveQRowCorrectToUnblockedOrBlocked E i₀)
  rw [Fintype.card_sum] at hsplit
  have hunblocked :=
    v13RealLinearAdaptiveQRow_unblockedCorrect_card_le_incorrect E i₀
  omega

theorem v13RealLinearAdaptiveQRow_world_card_eq_correct_add_incorrect
    {m q : Nat} {Seed : Type*} [Fintype Seed]
    (E : V13RealLinearAdaptiveQRowExperiment m q Seed) (i₀ : Fin m) :
    Fintype.card (V13RealLinearAdaptiveQRowWorld m Seed) =
      Fintype.card (V13RealLinearAdaptiveQRowCorrect E i₀) +
        Fintype.card (V13RealLinearAdaptiveQRowIncorrect E i₀) := by
  simpa [Fintype.card_sum] using
    Fintype.card_congr
      (v13RealLinearAdaptiveQRowWorldCorrectIncorrectEquiv E i₀)

/-- Explicit target error term for q row reads. -/
noncomputable def v13RealLinearQRowEpsilon (q m : Nat) : Rat :=
  (2 ^ q : Rat) / (2 ^ m : Rat)

theorem v13RealLinearAdaptiveQRowGeneratedMass_le_one
    {m q : Nat} {Seed : Type*} [Fintype Seed]
    (E : V13RealLinearAdaptiveQRowExperiment m q Seed) (i₀ : Fin m) :
    v13RealLinearAdaptiveQRowGeneratedMass E i₀ ≤ 1 := by
  classical
  unfold v13RealLinearAdaptiveQRowGeneratedMass
  let G := Fintype.card (V13RealLinearAdaptiveQRowGenerated E i₀)
  let T := Fintype.card (V13RealLinearAdaptiveQRowWorld m Seed)
  have hleNat : G ≤ T := by
    dsimp [G, T, V13RealLinearAdaptiveQRowGenerated]
    change
      Fintype.card
          {omega : V13RealLinearAdaptiveQRowWorld m Seed //
            E.generated i₀ omega} ≤
        Fintype.card (V13RealLinearAdaptiveQRowWorld m Seed)
    exact
      Fintype.card_subtype_le
        (fun omega : V13RealLinearAdaptiveQRowWorld m Seed =>
          E.generated i₀ omega)
  change (G : Rat) / (T : Rat) ≤ 1
  by_cases hTzero : T = 0
  · simp [hTzero]
  · have hTposNat : 0 < T := Nat.pos_of_ne_zero hTzero
    have hTpos : (0 : Rat) < (T : Rat) := by
      exact_mod_cast hTposNat
    rw [div_le_iff₀ hTpos]
    have hleRat : (G : Rat) ≤ (T : Rat) := by
      exact_mod_cast hleNat
    nlinarith

theorem v13RealLinear_qrow_one_le_epsilon_of_m_le_q {m q : Nat}
    (hmq : m ≤ q) :
    (1 : Rat) ≤ v13RealLinearQRowEpsilon q m := by
  unfold v13RealLinearQRowEpsilon
  have hpowNat : 2 ^ m ≤ 2 ^ q :=
    Nat.pow_le_pow_right (by norm_num : 0 < 2) hmq
  have hpowRat : (2 ^ m : Rat) ≤ (2 ^ q : Rat) := by
    exact_mod_cast hpowNat
  have hdenpos : (0 : Rat) < (2 ^ m : Rat) := by
    positivity
  rw [le_div_iff₀ hdenpos]
  simpa using hpowRat

/-- Generic blocked-mass bound used as an arithmetic interface.  The public
remaining pin below specializes this to the uniform invertible-map sampler. -/
def V13RealLinearAdaptiveRowSpanCountingBound {m q : Nat}
    {Seed : Type*} [Fintype Seed]
    (E : V13RealLinearAdaptiveQRowExperiment m q Seed) (i₀ : Fin m) :
    Prop :=
  v13RealLinearAdaptiveQRowGeneratedMass E i₀ ≤
    v13RealLinearQRowEpsilon q m

theorem v13RealLinearAdaptiveRowSpanCountingBound_of_zero_budget
    {m : Nat} {Seed : Type*} [Fintype Seed]
    (E : V13RealLinearAdaptiveQRowExperiment m 0 Seed) (i₀ : Fin m) :
    V13RealLinearAdaptiveRowSpanCountingBound E i₀ := by
  unfold V13RealLinearAdaptiveRowSpanCountingBound
  rw [v13RealLinearAdaptiveQRowGeneratedMass_eq_zero_of_zero_budget E i₀]
  unfold v13RealLinearQRowEpsilon
  positivity

theorem v13RealLinearAdaptiveRowSpanCountingBound_of_m_le_q
    {m q : Nat} {Seed : Type*} [Fintype Seed]
    (E : V13RealLinearAdaptiveQRowExperiment m q Seed) (i₀ : Fin m)
    (hmq : m ≤ q) :
    V13RealLinearAdaptiveRowSpanCountingBound E i₀ := by
  unfold V13RealLinearAdaptiveRowSpanCountingBound
  exact
    (v13RealLinearAdaptiveQRowGeneratedMass_le_one E i₀).trans
      (v13RealLinear_qrow_one_le_epsilon_of_m_le_q hmq)

/-- The single named pinned obligation: under the uniform sampler over all
certified invertible maps, the realized branch generates the target functional
from its read rows with mass at most `2^q / 2^m`. -/
def V13RealLinearUniformInvertibleRowSpanCountingBound {m q : Nat}
    (observer : V13RealLinearAdaptiveRowObserver m q) (i₀ : Fin m) : Prop :=
  V13RealLinearAdaptiveRowSpanCountingBound
    (v13RealLinearUniformQRowExperiment observer) i₀

theorem v13RealLinearUniformInvertibleRowSpanCountingBound_of_zero_budget
    {m : Nat} (observer : V13RealLinearAdaptiveRowObserver m 0)
    (i₀ : Fin m) :
    V13RealLinearUniformInvertibleRowSpanCountingBound observer i₀ :=
  v13RealLinearAdaptiveRowSpanCountingBound_of_zero_budget
    (v13RealLinearUniformQRowExperiment observer) i₀

theorem v13RealLinearUniformInvertibleRowSpanCountingBound_of_m_le_q
    {m q : Nat} (observer : V13RealLinearAdaptiveRowObserver m q)
    (i₀ : Fin m) (hmq : m ≤ q) :
    V13RealLinearUniformInvertibleRowSpanCountingBound observer i₀ :=
  v13RealLinearAdaptiveRowSpanCountingBound_of_m_le_q
    (v13RealLinearUniformQRowExperiment observer) i₀ hmq

noncomputable def v13RealLinearUniformAdaptiveQRowSuccess {m q : Nat}
    (observer : V13RealLinearAdaptiveRowObserver m q) (i₀ : Fin m) : Rat :=
  v13RealLinearAdaptiveQRowSuccess
    (v13RealLinearUniformQRowExperiment observer) i₀

/-- Kernel-flip branch pairing reduces success to half plus the blocked-branch
mass.  This is not a pinned counting assumption; it is the arithmetic interface
fed by the adaptive branch exact-half theorem. -/
def V13RealLinearAdaptiveKernelFlipSurchargeBound {m q : Nat}
    {Seed : Type*} [Fintype Seed]
    (E : V13RealLinearAdaptiveQRowExperiment m q Seed) (i₀ : Fin m) :
    Prop :=
  v13RealLinearAdaptiveQRowSuccess E i₀ ≤
    (1 / 2 : Rat) + v13RealLinearAdaptiveQRowBlockedMass E i₀

theorem v13RealLinear_adaptiveKernelFlipSurchargeBound
    {m q : Nat} {Seed : Type*} [Fintype Seed]
    (E : V13RealLinearAdaptiveQRowExperiment m q Seed) (i₀ : Fin m) :
    V13RealLinearAdaptiveKernelFlipSurchargeBound E i₀ := by
  classical
  unfold V13RealLinearAdaptiveKernelFlipSurchargeBound
  unfold v13RealLinearAdaptiveQRowSuccess
  unfold v13RealLinearAdaptiveQRowBlockedMass
  let C := Fintype.card (V13RealLinearAdaptiveQRowCorrect E i₀)
  let I := Fintype.card (V13RealLinearAdaptiveQRowIncorrect E i₀)
  let B := Fintype.card (V13RealLinearAdaptiveQRowBlocked E i₀)
  let T := Fintype.card (V13RealLinearAdaptiveQRowWorld m Seed)
  have hcardNat : C ≤ I + B := by
    simpa [C, I, B] using
      v13RealLinearAdaptiveQRow_correct_card_le_incorrect_add_blocked E i₀
  have hworldNat : T = C + I := by
    simpa [T, C, I] using
      v13RealLinearAdaptiveQRow_world_card_eq_correct_add_incorrect E i₀
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
    nlinarith

theorem v13RealLinear_adaptive_qrow_success_bound_of_spanCounting
    {m q : Nat} {Seed : Type*} [Fintype Seed]
    (E : V13RealLinearAdaptiveQRowExperiment m q Seed) (i₀ : Fin m)
    (hcount : V13RealLinearAdaptiveRowSpanCountingBound E i₀) :
    v13RealLinearAdaptiveQRowSuccess E i₀ ≤
      (1 / 2 : Rat) + v13RealLinearQRowEpsilon q m := by
  unfold V13RealLinearAdaptiveRowSpanCountingBound at hcount
  have hflip := v13RealLinear_adaptiveKernelFlipSurchargeBound E i₀
  unfold V13RealLinearAdaptiveKernelFlipSurchargeBound at hflip
  have hblocked :
      v13RealLinearAdaptiveQRowBlockedMass E i₀ ≤
        v13RealLinearQRowEpsilon q m := by
    rw [v13RealLinearAdaptiveQRowBlockedMass_eq_generatedMass E i₀]
    exact hcount
  linarith

theorem v13RealLinear_uniform_adaptive_qrow_success_bound_of_spanCounting
    {m q : Nat} (observer : V13RealLinearAdaptiveRowObserver m q)
    (i₀ : Fin m)
    (hcount :
      V13RealLinearUniformInvertibleRowSpanCountingBound observer i₀) :
    v13RealLinearUniformAdaptiveQRowSuccess observer i₀ ≤
      (1 / 2 : Rat) + v13RealLinearQRowEpsilon q m := by
  exact
    v13RealLinear_adaptive_qrow_success_bound_of_spanCounting
      (v13RealLinearUniformQRowExperiment observer) i₀ hcount

theorem v13RealLinear_uniform_zero_row_success_bound
    {m : Nat} (observer : V13RealLinearAdaptiveRowObserver m 0)
    (i₀ : Fin m) :
    v13RealLinearUniformAdaptiveQRowSuccess observer i₀ ≤
      (1 / 2 : Rat) + v13RealLinearQRowEpsilon 0 m := by
  exact
    v13RealLinear_uniform_adaptive_qrow_success_bound_of_spanCounting
      observer i₀
      (v13RealLinearUniformInvertibleRowSpanCountingBound_of_zero_budget
        observer i₀)

theorem v13RealLinear_uniform_high_budget_success_bound
    {m q : Nat} (observer : V13RealLinearAdaptiveRowObserver m q)
    (i₀ : Fin m) (hmq : m ≤ q) :
    v13RealLinearUniformAdaptiveQRowSuccess observer i₀ ≤
      (1 / 2 : Rat) + v13RealLinearQRowEpsilon q m := by
  exact
    v13RealLinear_uniform_adaptive_qrow_success_bound_of_spanCounting
      observer i₀
      (v13RealLinearUniformInvertibleRowSpanCountingBound_of_m_le_q
        observer i₀ hmq)

theorem v13RealLinear_qrow_epsilon_nonnegative (q m : Nat) :
    0 ≤ v13RealLinearQRowEpsilon q m := by
  unfold v13RealLinearQRowEpsilon
  positivity

end Mettapedia.Computability.PNP
