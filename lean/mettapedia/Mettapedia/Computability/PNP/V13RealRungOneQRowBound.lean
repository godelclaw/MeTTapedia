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

/-- Causal q-row observers choose their realized branch from the public row
transcript of that branch, not from the full sampled map.  This is the refined
interface needed after the full-map target-row chooser obstruction. -/
structure V13RealLinearCausalRowObserver (m q : Nat) where
  Branch : Type
  branch : V13RealLinearPublic m → Branch
  rows : Branch → Finset (Fin m)
  decideFromTranscript :
    ∀ b : Branch,
      ({row : Fin m // row ∈ rows b} → V13RealLinearRowView m) → ZMod 2
  readBudget : ∀ b : Branch, (rows b).card ≤ q
  branchCausal :
    ∀ (public₀ public₁ : V13RealLinearPublic m) (b : Branch),
      branch public₀ = b →
        v13RealLinearRowsTranscript (rows b) public₀ =
          v13RealLinearRowsTranscript (rows b) public₁ →
        branch public₁ = b

def V13RealLinearCausalRowObserver.staticBranch {m q : Nat}
    (observer : V13RealLinearCausalRowObserver m q)
    (b : observer.Branch) : V13RealLinearStaticRowObserver m q where
  rows := observer.rows b
  decide := fun omega =>
    observer.decideFromTranscript b
      (v13RealLinearRowsTranscript (observer.rows b)
        (v13RealLinearPublicInput omega))
  readBudget := observer.readBudget b
  factorsThroughRows := by
    intro omega₀ omega₁ hsame
    exact congrArg (observer.decideFromTranscript b) hsame

def V13RealLinearCausalRowObserver.toAdaptive {m q : Nat}
    (observer : V13RealLinearCausalRowObserver m q) :
    V13RealLinearAdaptiveRowObserver m q where
  Branch := observer.Branch
  branch := fun omega => observer.branch (v13RealLinearPublicInput omega)
  staticBranch := observer.staticBranch
  decide := fun omega =>
    let b := observer.branch (v13RealLinearPublicInput omega)
    observer.decideFromTranscript b
      (v13RealLinearRowsTranscript (observer.rows b)
        (v13RealLinearPublicInput omega))
  branchDecision := by
    intro omega
    rfl
  branchStable := by
    intro A x w b hbranch hkernel
    apply observer.branchCausal
      (v13RealLinearPublicInput
        ({ x := x, A := A } : V13RealLinearWorld m))
      (v13RealLinearPublicInput
        ({ x := f2AddVec x w, A := A } : V13RealLinearWorld m))
      b hbranch
    exact
      v13RealLinear_same_rowsTranscript_after_kernel_add
        A x w (observer.rows b) hkernel

theorem V13RealLinearCausalRowObserver.branch_eq_of_same_branchRowsTranscript
    {m q : Nat} (observer : V13RealLinearCausalRowObserver m q)
    (public₀ public₁ : V13RealLinearPublic m)
    (hsame :
      v13RealLinearRowsTranscript
          (observer.rows (observer.branch public₀)) public₀ =
        v13RealLinearRowsTranscript
          (observer.rows (observer.branch public₀)) public₁) :
    observer.branch public₁ = observer.branch public₀ := by
  exact
    observer.branchCausal public₀ public₁ (observer.branch public₀) rfl
      hsame

noncomputable def v13RealLinearUniformCausalQRowExperiment {m q : Nat}
    (observer : V13RealLinearCausalRowObserver m q) :
    V13RealLinearAdaptiveQRowExperiment m q (V13F2LinearEquiv m) :=
  v13RealLinearUniformQRowExperiment observer.toAdaptive

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

/-- A row-combination certificate that a fixed rowset generates the target
coordinate for a fixed invertible map. -/
def V13RealLinearRowsTargetCoefficient {m : Nat}
    (A : V13F2LinearEquiv m) (rows : Finset (Fin m)) (i₀ : Fin m) :=
  {coeff : V13RealLinearRowCombination rows //
    ∀ w : F2Vec m,
      v13RealLinearRowCombinationEval A rows coeff w = w i₀}

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

noncomputable instance {m : Nat} (A : V13F2LinearEquiv m)
    (rows : Finset (Fin m)) (i₀ : Fin m) :
    Fintype (V13RealLinearRowsTargetCoefficient A rows i₀) := by
  classical
  unfold V13RealLinearRowsTargetCoefficient
  infer_instance

noncomputable def v13RealLinearRowsTargetCoefficientEmbedding {m : Nat}
    (A : V13F2LinearEquiv m) (rows : Finset (Fin m)) (i₀ : Fin m) :
    V13RealLinearRowsTargetCoefficient A rows i₀ ↪
      V13RealLinearRowCombination rows where
  toFun coeff := coeff.val
  inj' := by
    intro coeff₀ coeff₁ hcoeff
    exact Subtype.ext hcoeff

theorem v13RealLinear_rowsTargetCoefficient_card_le_rowCombination {m : Nat}
    (A : V13F2LinearEquiv m) (rows : Finset (Fin m)) (i₀ : Fin m) :
    Fintype.card (V13RealLinearRowsTargetCoefficient A rows i₀) ≤
      Fintype.card (V13RealLinearRowCombination rows) := by
  classical
  exact Fintype.card_le_of_embedding
    (v13RealLinearRowsTargetCoefficientEmbedding A rows i₀)

theorem v13RealLinear_rowsTargetCoefficient_card_le_of_rows_card_le
    {m q : Nat} (A : V13F2LinearEquiv m)
    {rows : Finset (Fin m)} (i₀ : Fin m) (hrows : rows.card ≤ q) :
    Fintype.card (V13RealLinearRowsTargetCoefficient A rows i₀) ≤
      2 ^ q := by
  calc
    Fintype.card (V13RealLinearRowsTargetCoefficient A rows i₀) ≤
        Fintype.card (V13RealLinearRowCombination rows) :=
      v13RealLinear_rowsTargetCoefficient_card_le_rowCombination A rows i₀
    _ ≤ 2 ^ q := v13RealLinear_rowCombination_card_le_of_rows_card_le hrows

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

theorem v13RealLinear_singletonRowCombination_eq_one_of_generates {m : Nat}
    (A : V13F2LinearEquiv m) (row i₀ : Fin m)
    (coeff : V13RealLinearRowCombination ({row} : Finset (Fin m)))
    (hcoeff : ∀ w : F2Vec m,
      v13RealLinearRowCombinationEval A ({row} : Finset (Fin m))
        coeff w = w i₀) :
    coeff = fun _ => 1 := by
  classical
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
  funext r
  have hr :
      r = (default : {r : Fin m // r ∈ ({row} : Finset (Fin m))}) :=
    Subsingleton.elim _ _
  rw [hr]
  exact hc

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

def v13RealLinearCausalSingleRowObserver {m : Nat} (row : Fin m) :
    V13RealLinearCausalRowObserver m 1 where
  Branch := Unit
  branch := fun _ => ()
  rows := fun _ => {row}
  decideFromTranscript := fun _ transcript =>
    (transcript ⟨row, by simp⟩).2
  readBudget := by
    intro b
    cases b
    simp
  branchCausal := by
    intro public₀ public₁ b hbranch htranscript
    cases b
    rfl

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

theorem V13RealLinearAdaptiveQRowExperiment.generated_one_budget_exists_singleton_target_row
    {m : Nat} {Seed : Type*}
    (E : V13RealLinearAdaptiveQRowExperiment m 1 Seed) (i₀ : Fin m)
    (omega : V13RealLinearAdaptiveQRowWorld m Seed)
    (hgen : E.generated i₀ omega) :
    ∃ row : Fin m,
      E.branchRows omega = ({row} : Finset (Fin m)) ∧
        row ∈ V13RealLinearTargetRows (E.sampleA omega.1) i₀ := by
  classical
  have hcardLe : (E.branchRows omega).card ≤ 1 :=
    E.branchRows_card_le omega
  have hcardNe : (E.branchRows omega).card ≠ 0 := by
    intro hzero
    exact (E.not_generated_of_branchRows_card_zero i₀ omega hzero) hgen
  have hcard : (E.branchRows omega).card = 1 := by
    omega
  rcases Finset.card_eq_one.mp hcard with ⟨row, hrows⟩
  have hsingleton :
      V13RealLinearRowsGenerateTarget
        (E.sampleA omega.1) ({row} : Finset (Fin m)) i₀ := by
    simpa [V13RealLinearAdaptiveQRowExperiment.generated, hrows] using hgen
  have htarget :
      ∀ w : F2Vec m, (E.sampleA omega.1).toEquiv w row = w i₀ :=
    (v13RealLinear_rowsGenerateTarget_singleton_iff
      (E.sampleA omega.1) row i₀).1 hsingleton
  exact
    ⟨row, hrows,
      (v13RealLinear_mem_targetRows_iff
        (E.sampleA omega.1) i₀ row).2 htarget⟩

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

theorem V13RealLinearAdaptiveQRowExperiment.not_generated_of_targetRows_empty
    {m : Nat} {Seed : Type*}
    (E : V13RealLinearAdaptiveQRowExperiment m 1 Seed) (i₀ : Fin m)
    (omega : V13RealLinearAdaptiveQRowWorld m Seed)
    (hempty : V13RealLinearTargetRows (E.sampleA omega.1) i₀ = ∅) :
    ¬ E.generated i₀ omega := by
  intro hgen
  have hnonempty :=
    E.targetRows_nonempty_of_generated_one_budget i₀ omega hgen
  rw [hempty] at hnonempty
  exact Finset.not_nonempty_empty hnonempty

theorem v13RealLinearUniformCausalOneRowGenerated_exists_targetRow_cylinder
    {m : Nat} (observer : V13RealLinearCausalRowObserver m 1)
    (i₀ : Fin m)
    (omega : V13RealLinearAdaptiveQRowWorld m (V13F2LinearEquiv m))
    (hgen :
      (v13RealLinearUniformCausalQRowExperiment observer).generated
        i₀ omega) :
    ∃ row : Fin m,
      (v13RealLinearUniformCausalQRowExperiment observer).branchRows omega =
          ({row} : Finset (Fin m)) ∧
        row ∈ V13RealLinearTargetRows omega.1 i₀ ∧
          ∀ omega' : V13RealLinearAdaptiveQRowWorld m (V13F2LinearEquiv m),
            v13RealLinearRowsTranscript ({row} : Finset (Fin m))
                (v13RealLinearPublicInput
                  ((v13RealLinearUniformCausalQRowExperiment observer).world
                    omega)) =
              v13RealLinearRowsTranscript ({row} : Finset (Fin m))
                (v13RealLinearPublicInput
                  ((v13RealLinearUniformCausalQRowExperiment observer).world
                    omega')) →
            observer.branch
                (v13RealLinearPublicInput
                  ((v13RealLinearUniformCausalQRowExperiment observer).world
                    omega')) =
              observer.branch
                (v13RealLinearPublicInput
                  ((v13RealLinearUniformCausalQRowExperiment observer).world
                    omega)) := by
  classical
  let E := v13RealLinearUniformCausalQRowExperiment observer
  rcases
      E.generated_one_budget_exists_singleton_target_row i₀ omega hgen with
    ⟨row, hrows, htarget⟩
  refine ⟨row, hrows, ?_, ?_⟩
  · simpa [E, v13RealLinearUniformCausalQRowExperiment,
      v13RealLinearUniformQRowExperiment] using htarget
  · intro omega' hsame
    let public₀ :=
      v13RealLinearPublicInput
        ((v13RealLinearUniformCausalQRowExperiment observer).world omega)
    let public₁ :=
      v13RealLinearPublicInput
        ((v13RealLinearUniformCausalQRowExperiment observer).world omega')
    have hrowsObserver :
        observer.rows (observer.branch public₀) =
          ({row} : Finset (Fin m)) := by
      simpa [public₀, E,
        V13RealLinearAdaptiveQRowExperiment.branchRows,
        V13RealLinearAdaptiveQRowExperiment.branch,
        V13RealLinearCausalRowObserver.toAdaptive,
        V13RealLinearCausalRowObserver.staticBranch,
        v13RealLinearUniformCausalQRowExperiment,
        v13RealLinearUniformQRowExperiment] using hrows
    have hsameBranch :
        v13RealLinearRowsTranscript
            (observer.rows (observer.branch public₀)) public₀ =
          v13RealLinearRowsTranscript
            (observer.rows (observer.branch public₀)) public₁ := by
      rw [hrowsObserver]
      simpa [public₀, public₁] using hsame
    exact
      observer.branch_eq_of_same_branchRowsTranscript
        public₀ public₁ hsameBranch

theorem v13RealLinearUniformCausalOneRowGenerated_exists_generated_cylinder
    {m : Nat} (observer : V13RealLinearCausalRowObserver m 1)
    (i₀ : Fin m)
    (omega : V13RealLinearAdaptiveQRowWorld m (V13F2LinearEquiv m))
    (hgen :
      (v13RealLinearUniformCausalQRowExperiment observer).generated
        i₀ omega) :
    ∃ row : Fin m,
      (v13RealLinearUniformCausalQRowExperiment observer).branchRows omega =
          ({row} : Finset (Fin m)) ∧
        row ∈ V13RealLinearTargetRows omega.1 i₀ ∧
          ∀ omega' : V13RealLinearAdaptiveQRowWorld m (V13F2LinearEquiv m),
            v13RealLinearRowsTranscript ({row} : Finset (Fin m))
                (v13RealLinearPublicInput
                  ((v13RealLinearUniformCausalQRowExperiment observer).world
                    omega)) =
              v13RealLinearRowsTranscript ({row} : Finset (Fin m))
                (v13RealLinearPublicInput
                  ((v13RealLinearUniformCausalQRowExperiment observer).world
                    omega')) →
            (v13RealLinearUniformCausalQRowExperiment observer).generated
              i₀ omega' := by
  classical
  let E := v13RealLinearUniformCausalQRowExperiment observer
  rcases
      v13RealLinearUniformCausalOneRowGenerated_exists_targetRow_cylinder
        observer i₀ omega hgen with
    ⟨row, hrows, htarget, hcylinder⟩
  refine ⟨row, hrows, htarget, ?_⟩
  intro omega' hsame
  have hbranch :
      observer.branch
          (v13RealLinearPublicInput
            ((v13RealLinearUniformCausalQRowExperiment observer).world
              omega')) =
        observer.branch
          (v13RealLinearPublicInput
            ((v13RealLinearUniformCausalQRowExperiment observer).world
              omega)) :=
    hcylinder omega' hsame
  have hbranchRows' :
      (v13RealLinearUniformCausalQRowExperiment observer).branchRows omega' =
          ({row} : Finset (Fin m)) := by
    have hrowsEq :=
      congrArg observer.rows hbranch
    have hrowsOmega :
        observer.rows
            (observer.branch
              (v13RealLinearPublicInput
                ((v13RealLinearUniformCausalQRowExperiment observer).world
                  omega))) =
          ({row} : Finset (Fin m)) := by
      simpa [v13RealLinearUniformCausalQRowExperiment,
        v13RealLinearUniformQRowExperiment,
        V13RealLinearAdaptiveQRowExperiment.branchRows,
        V13RealLinearAdaptiveQRowExperiment.branch,
        V13RealLinearCausalRowObserver.toAdaptive,
        V13RealLinearCausalRowObserver.staticBranch] using hrows
    simpa [v13RealLinearUniformCausalQRowExperiment,
      v13RealLinearUniformQRowExperiment,
      V13RealLinearAdaptiveQRowExperiment.branchRows,
      V13RealLinearAdaptiveQRowExperiment.branch,
      V13RealLinearCausalRowObserver.toAdaptive,
      V13RealLinearCausalRowObserver.staticBranch] using hrowsEq.trans hrowsOmega
  have hview :
      v13RealLinearRowView row
          (v13RealLinearPublicInput
            ((v13RealLinearUniformCausalQRowExperiment observer).world
              omega)) =
        v13RealLinearRowView row
          (v13RealLinearPublicInput
            ((v13RealLinearUniformCausalQRowExperiment observer).world
              omega')) := by
    simpa [v13RealLinearRowsTranscript] using
      congrFun hsame ⟨row, by simp⟩
  have hrowFunctional :
      (fun probe : F2Vec m => omega.1.toEquiv probe row) =
        (fun probe : F2Vec m => omega'.1.toEquiv probe row) := by
    simpa [v13RealLinearRowView, v13RealLinearPublicInput,
      V13RealLinearAdaptiveQRowExperiment.world,
      v13RealLinearUniformCausalQRowExperiment,
      v13RealLinearUniformQRowExperiment] using congrArg Prod.fst hview
  have htarget' :
      ∀ w : F2Vec m, omega'.1.toEquiv w row = w i₀ := by
    intro w
    have htargetFun :
        ∀ probe : F2Vec m, omega.1.toEquiv probe row = probe i₀ :=
      (v13RealLinear_mem_targetRows_iff omega.1 i₀ row).1 htarget
    have hfunAt := congrFun hrowFunctional w
    calc
      omega'.1.toEquiv w row = omega.1.toEquiv w row := hfunAt.symm
      _ = w i₀ := htargetFun w
  change
    V13RealLinearRowsGenerateTarget omega'.1
      ((v13RealLinearUniformCausalQRowExperiment observer).branchRows omega')
      i₀
  rw [hbranchRows']
  exact
    (v13RealLinear_rowsGenerateTarget_singleton_iff omega'.1 row i₀).2
      htarget'

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

def V13RealLinearUniformFixedTargetRowOccurrence {m : Nat}
    (row i₀ : Fin m) :=
  {A : V13F2LinearEquiv m // row ∈ V13RealLinearTargetRows A i₀}

structure V13RealLinearRowIndexedFixedTargetRowOccurrenceWorld
    (m : Nat) (i₀ : Fin m) where
  row : Fin m
  A : V13F2LinearEquiv m
  x : F2Vec m
  targetRow : row ∈ V13RealLinearTargetRows A i₀

noncomputable def v13RealLinearRowIndexedFixedTargetRowOccurrenceWorldEquiv
    {m : Nat} (i₀ : Fin m) :
    V13RealLinearRowIndexedFixedTargetRowOccurrenceWorld m i₀ ≃
      (Σ row : Fin m,
        V13RealLinearUniformFixedTargetRowOccurrence row i₀ × F2Vec m) where
  toFun data :=
    ⟨data.row, (⟨data.A, data.targetRow⟩, data.x)⟩
  invFun data :=
    { row := data.1
      A := data.2.1.val
      x := data.2.2
      targetRow := data.2.1.property }
  left_inv := by
    intro data
    cases data
    rfl
  right_inv := by
    intro data
    cases data with
    | mk row rest =>
        cases rest with
        | mk occ x =>
            cases occ
            rfl

noncomputable instance {m : Nat} (row i₀ : Fin m) :
    Fintype (V13RealLinearUniformFixedTargetRowOccurrence row i₀) := by
  classical
  unfold V13RealLinearUniformFixedTargetRowOccurrence
  infer_instance

noncomputable instance {m : Nat} (i₀ : Fin m) :
    Fintype (V13RealLinearRowIndexedFixedTargetRowOccurrenceWorld m i₀) := by
  classical
  exact
    Fintype.ofEquiv
      (Σ row : Fin m,
        V13RealLinearUniformFixedTargetRowOccurrence row i₀ × F2Vec m)
      (v13RealLinearRowIndexedFixedTargetRowOccurrenceWorldEquiv i₀).symm

/-- Vectors whose selected coordinate is zero.  These index the elementary
row transvections used to spread one fixed target row through a half-space of
possible row functionals. -/
def V13RealLinearZeroAt {m : Nat} (i₀ : Fin m) :=
  {s : F2Vec m // s i₀ = 0}

noncomputable instance {m : Nat} (i₀ : Fin m) :
    Fintype (V13RealLinearZeroAt i₀) := by
  classical
  unfold V13RealLinearZeroAt
  infer_instance

noncomputable def v13RealLinearZeroAtProdBitEquiv {m : Nat} (i₀ : Fin m) :
    V13RealLinearZeroAt i₀ × ZMod 2 ≃ F2Vec m where
  toFun pair := fun j => if j = i₀ then pair.2 else pair.1.val j
  invFun w :=
    (⟨fun j => if j = i₀ then 0 else w j, by simp⟩, w i₀)
  left_inv pair := by
    apply Prod.ext
    · apply Subtype.ext
      funext j
      by_cases hj : j = i₀
      · simp [hj, pair.1.property]
      · simp [hj]
    · simp
  right_inv w := by
    funext j
    by_cases hj : j = i₀ <;> simp [hj]

theorem v13RealLinear_zeroAt_card_mul_two {m : Nat} (i₀ : Fin m) :
    Fintype.card (V13RealLinearZeroAt i₀) * 2 = 2 ^ m := by
  classical
  have hcard :=
    Fintype.card_congr (v13RealLinearZeroAtProdBitEquiv i₀)
  rw [Fintype.card_prod] at hcard
  have hzmod : Fintype.card (ZMod 2) = 2 := by
    simp
  have hf2 : Fintype.card (F2Vec m) = 2 ^ m := by
    simp [F2Vec]
  simpa [hzmod, hf2] using hcard

/-- Vectors whose selected coordinate is a fixed bit. -/
def V13RealLinearBitAt {m : Nat} (i₀ : Fin m) (bit : ZMod 2) :=
  {x : F2Vec m // x i₀ = bit}

noncomputable instance {m : Nat} (i₀ : Fin m) (bit : ZMod 2) :
    Fintype (V13RealLinearBitAt i₀ bit) := by
  classical
  unfold V13RealLinearBitAt
  infer_instance

noncomputable def v13RealLinearBitAtZeroAtEquiv {m : Nat}
    (i₀ : Fin m) (bit : ZMod 2) :
    V13RealLinearBitAt i₀ bit ≃ V13RealLinearZeroAt i₀ where
  toFun x :=
    ⟨fun j => if j = i₀ then 0 else x.val j, by simp⟩
  invFun z :=
    ⟨fun j => if j = i₀ then bit else z.val j, by simp⟩
  left_inv x := by
    apply Subtype.ext
    funext j
    by_cases hj : j = i₀
    · subst j
      simp [x.property]
    · simp [hj]
  right_inv z := by
    apply Subtype.ext
    funext j
    by_cases hj : j = i₀
    · subst j
      simp [z.property]
    · simp [hj]

theorem v13RealLinear_bitAt_card_mul_two {m : Nat}
    (i₀ : Fin m) (bit : ZMod 2) :
    Fintype.card (V13RealLinearBitAt i₀ bit) * 2 = 2 ^ m := by
  classical
  rw [Fintype.card_congr (v13RealLinearBitAtZeroAtEquiv i₀ bit)]
  exact v13RealLinear_zeroAt_card_mul_two i₀

/-- A fixed target-row occurrence together with one fixed row-transcript RHS
bit.  When the row is the target row, the RHS bit is exactly the hidden target
coordinate. -/
structure V13RealLinearUniformFixedTargetRowBitCylinder {m : Nat}
    (row i₀ : Fin m) (bit : ZMod 2) where
  A : V13F2LinearEquiv m
  x : F2Vec m
  targetRow : row ∈ V13RealLinearTargetRows A i₀
  targetBit : x i₀ = bit

noncomputable def v13RealLinearFixedTargetRowBitCylinderEquiv
    {m : Nat} (row i₀ : Fin m) (bit : ZMod 2) :
    V13RealLinearUniformFixedTargetRowBitCylinder row i₀ bit ≃
      V13RealLinearUniformFixedTargetRowOccurrence row i₀ ×
        V13RealLinearBitAt i₀ bit where
  toFun data :=
    (⟨data.A, data.targetRow⟩, ⟨data.x, data.targetBit⟩)
  invFun data :=
    { A := data.1.val
      x := data.2.val
      targetRow := data.1.property
      targetBit := data.2.property }
  left_inv data := by
    cases data
    rfl
  right_inv data := by
    cases data with
    | mk occ x =>
        cases occ
        cases x
        rfl

noncomputable instance {m : Nat} (row i₀ : Fin m) (bit : ZMod 2) :
    Fintype (V13RealLinearUniformFixedTargetRowBitCylinder row i₀ bit) := by
  classical
  exact
    Fintype.ofEquiv
      (V13RealLinearUniformFixedTargetRowOccurrence row i₀ ×
        V13RealLinearBitAt i₀ bit)
      (v13RealLinearFixedTargetRowBitCylinderEquiv row i₀ bit).symm

theorem v13RealLinearFixedTargetRowBitCylinder_card_eq
    {m : Nat} (row i₀ : Fin m) (bit : ZMod 2) :
    Fintype.card
        (V13RealLinearUniformFixedTargetRowBitCylinder row i₀ bit) =
      Fintype.card (V13RealLinearUniformFixedTargetRowOccurrence row i₀) *
        Fintype.card (V13RealLinearBitAt i₀ bit) := by
  classical
  rw [Fintype.card_congr
    (v13RealLinearFixedTargetRowBitCylinderEquiv row i₀ bit)]
  rw [Fintype.card_prod]

def v13RealLinearZeroAtShearSum {m : Nat} (i₀ : Fin m)
    (s : V13RealLinearZeroAt i₀) (w : F2Vec m) : ZMod 2 :=
  (Finset.univ.erase i₀).sum (fun j => s.val j * w j)

theorem v13RealLinearZeroAtShearSum_apply_shear {m : Nat} (i₀ : Fin m)
    (s : V13RealLinearZeroAt i₀) (w : F2Vec m) :
    v13RealLinearZeroAtShearSum i₀ s
        (fun r => if r = i₀ then
          w i₀ + v13RealLinearZeroAtShearSum i₀ s w else w r) =
      v13RealLinearZeroAtShearSum i₀ s w := by
  classical
  unfold v13RealLinearZeroAtShearSum
  apply Finset.sum_congr rfl
  intro j hj
  have hne : j ≠ i₀ := by
    exact (Finset.mem_erase.mp hj).1
  simp [hne]

/-- A row transvection that changes the selected output row functional from
`e_i` to `e_i + s`, where `s i = 0`, and fixes every other coordinate. -/
def v13RealLinearZeroAtRowShear {m : Nat} (i₀ : Fin m)
    (s : V13RealLinearZeroAt i₀) : V13F2LinearEquiv m where
  toEquiv :=
    { toFun := fun w r =>
        if r = i₀ then w i₀ + v13RealLinearZeroAtShearSum i₀ s w else w r
      invFun := fun w r =>
        if r = i₀ then w i₀ + v13RealLinearZeroAtShearSum i₀ s w else w r
      left_inv := by
        intro w
        funext r
        by_cases hr : r = i₀
        · subst r
          simp [v13RealLinearZeroAtShearSum_apply_shear,
            f2_add_right_self]
        · simp [hr]
      right_inv := by
        intro w
        funext r
        by_cases hr : r = i₀
        · subst r
          simp [v13RealLinearZeroAtShearSum_apply_shear,
            f2_add_right_self]
        · simp [hr] }
  map_add := by
    intro x y
    funext r
    by_cases hr : r = i₀
    · subst r
      unfold v13RealLinearZeroAtShearSum
      simp [f2AddVec, Finset.sum_add_distrib, mul_add]
      ring
    · simp [f2AddVec, hr]
  map_zero := by
    funext r
    by_cases hr : r = i₀
    · subst r
      simp [f2ZeroVec, v13RealLinearZeroAtShearSum]
    · simp [f2ZeroVec, hr]

theorem v13RealLinearZeroAtRowShear_row_apply_singleBit_of_ne {m : Nat}
    {i₀ j : Fin m} (s : V13RealLinearZeroAt i₀) (hne : j ≠ i₀) :
    (v13RealLinearZeroAtRowShear i₀ s).toEquiv
        (v13RealLinearSingleBit j) i₀ = s.val j := by
  classical
  have hne' : i₀ ≠ j := fun h => hne h.symm
  simp [v13RealLinearZeroAtRowShear, v13RealLinearZeroAtShearSum,
    v13RealLinearSingleBit, hne']

theorem v13RealLinearZeroAtRowShear_targetRows_empty_of_nonzero
    {m : Nat} (i₀ : Fin m) (s : V13RealLinearZeroAt i₀)
    (hs : ∃ j : Fin m, j ≠ i₀ ∧ s.val j = 1) :
    V13RealLinearTargetRows (v13RealLinearZeroAtRowShear i₀ s) i₀ = ∅ := by
  classical
  ext row
  constructor
  · intro hrow
    rcases hs with ⟨j, hjne, hsj⟩
    have htarget :
        ∀ w : F2Vec m,
          (v13RealLinearZeroAtRowShear i₀ s).toEquiv w row = w i₀ :=
      (v13RealLinear_mem_targetRows_iff
        (v13RealLinearZeroAtRowShear i₀ s) i₀ row).1 hrow
    by_cases hrowi : row = i₀
    · subst row
      have h := htarget (v13RealLinearSingleBit j)
      rw [v13RealLinearZeroAtRowShear_row_apply_singleBit_of_ne s hjne] at h
      simp [v13RealLinearSingleBit, hsj] at h
      exact (hjne h.symm).elim
    · have h := htarget (v13RealLinearSingleBit i₀)
      simp [v13RealLinearZeroAtRowShear, v13RealLinearSingleBit, hrowi] at h
  · intro hrow
    simp at hrow

def v13FinSpare {m : Nat} (i₀ : Fin m) (hm : 1 < m) : Fin m :=
  if _h : i₀.val = 0 then ⟨1, hm⟩
  else ⟨0, Nat.lt_trans Nat.zero_lt_one hm⟩

theorem v13FinSpare_ne {m : Nat} (i₀ : Fin m) (hm : 1 < m) :
    v13FinSpare i₀ hm ≠ i₀ := by
  classical
  unfold v13FinSpare
  by_cases h : i₀.val = 0
  · simp [h]
    intro heq
    have hval : 1 = i₀.val := congrArg Fin.val heq
    omega
  · simp [h]
    intro heq
    have hval : 0 = i₀.val := congrArg Fin.val heq
    exact h hval.symm

noncomputable def v13RealLinearNoTargetRowShear {m : Nat}
    (i₀ : Fin m) (hm : 1 < m) : V13F2LinearEquiv m :=
  v13RealLinearZeroAtRowShear i₀
    ⟨v13RealLinearSingleBit (v13FinSpare i₀ hm), by
      have hne : i₀ ≠ v13FinSpare i₀ hm :=
        fun h => v13FinSpare_ne i₀ hm h.symm
      simp [v13RealLinearSingleBit, hne]⟩

theorem v13RealLinearNoTargetRowShear_targetRows_empty {m : Nat}
    (i₀ : Fin m) (hm : 1 < m) :
    V13RealLinearTargetRows (v13RealLinearNoTargetRowShear i₀ hm) i₀ = ∅ := by
  classical
  unfold v13RealLinearNoTargetRowShear
  apply v13RealLinearZeroAtRowShear_targetRows_empty_of_nonzero
  exact ⟨v13FinSpare i₀ hm, v13FinSpare_ne i₀ hm, by
    simp [v13RealLinearSingleBit]⟩

theorem v13RealLinearNoTargetRowShear_rowFunctional_ne_target
    {m : Nat} (i₀ : Fin m) (hm : 1 < m) (row : Fin m) :
    ∃ w : F2Vec m,
      (v13RealLinearNoTargetRowShear i₀ hm).toEquiv w row ≠ w i₀ := by
  classical
  by_cases hrow : row = i₀
  · subst row
    let spare := v13FinSpare i₀ hm
    let s : V13RealLinearZeroAt i₀ :=
      ⟨v13RealLinearSingleBit spare, by
        have hne : i₀ ≠ spare := fun h => v13FinSpare_ne i₀ hm h.symm
        simp [spare, v13RealLinearSingleBit, hne]⟩
    refine ⟨v13RealLinearSingleBit spare, ?_⟩
    have hspare : spare ≠ i₀ := by
      simpa [spare] using v13FinSpare_ne i₀ hm
    have hleft :
        (v13RealLinearNoTargetRowShear i₀ hm).toEquiv
            (v13RealLinearSingleBit spare) i₀ = 1 := by
      have happly :
          (v13RealLinearZeroAtRowShear i₀ s).toEquiv
              (v13RealLinearSingleBit spare) i₀ = s.val spare :=
        v13RealLinearZeroAtRowShear_row_apply_singleBit_of_ne s
          (by simpa [spare] using v13FinSpare_ne i₀ hm)
      simpa [v13RealLinearNoTargetRowShear, s, spare,
        v13RealLinearSingleBit] using happly
    have hright : v13RealLinearSingleBit spare i₀ = 0 := by
      simp [v13RealLinearSingleBit, hspare.symm]
    intro heq
    rw [hleft, hright] at heq
    norm_num at heq
  · refine ⟨v13RealLinearSingleBit i₀, ?_⟩
    have hleft :
        (v13RealLinearNoTargetRowShear i₀ hm).toEquiv
            (v13RealLinearSingleBit i₀) row = 0 := by
      simp [v13RealLinearNoTargetRowShear, v13RealLinearZeroAtRowShear,
        v13RealLinearSingleBit, hrow]
    have hright : v13RealLinearSingleBit i₀ i₀ = 1 := by
      simp [v13RealLinearSingleBit]
    intro heq
    rw [hleft, hright] at heq
    norm_num at heq

theorem v13RealLinearNoTargetRowShear_row_not_mem_targetRows
    {m : Nat} (i₀ : Fin m) (hm : 1 < m) (row : Fin m) :
    row ∉ V13RealLinearTargetRows (v13RealLinearNoTargetRowShear i₀ hm) i₀ := by
  classical
  intro hrow
  rcases v13RealLinearNoTargetRowShear_rowFunctional_ne_target i₀ hm row with
    ⟨w, hw⟩
  exact
    hw ((v13RealLinear_mem_targetRows_iff
      (v13RealLinearNoTargetRowShear i₀ hm) i₀ row).1 hrow w)

theorem v13RealLinearNoTargetRowShear_rowFunctional_ne_activeTarget
    {m : Nat} (i₀ : Fin m) (hm : 1 < m)
    (A : V13F2LinearEquiv m) (restRow activeRow : Fin m)
    (htarget : activeRow ∈ V13RealLinearTargetRows A i₀) :
    ∃ w : F2Vec m,
      (v13RealLinearNoTargetRowShear i₀ hm).toEquiv w restRow ≠
        A.toEquiv w activeRow := by
  classical
  rcases
      v13RealLinearNoTargetRowShear_rowFunctional_ne_target
        i₀ hm restRow with
    ⟨w, hw⟩
  refine ⟨w, ?_⟩
  intro hsame
  have htargetFun :
      ∀ probe : F2Vec m, A.toEquiv probe activeRow = probe i₀ :=
    (v13RealLinear_mem_targetRows_iff A i₀ activeRow).1 htarget
  exact hw (hsame.trans (htargetFun w))

theorem v13RealLinearRowsTranscript_singleton_eq_of_row_match
    {m : Nat} (A B : V13F2LinearEquiv m) (x y : F2Vec m)
    (row : Fin m)
    (hfun : ∀ probe : F2Vec m, A.toEquiv probe row = B.toEquiv probe row)
    (hbit : A.toEquiv x row = B.toEquiv y row) :
    v13RealLinearRowsTranscript ({row} : Finset (Fin m))
        (v13RealLinearPublicInput
          ({ x := x, A := A } : V13RealLinearWorld m)) =
      v13RealLinearRowsTranscript ({row} : Finset (Fin m))
        (v13RealLinearPublicInput
          ({ x := y, A := B } : V13RealLinearWorld m)) := by
  classical
  funext observed
  rcases observed with ⟨observedRow, hobservedRow⟩
  have hrow : observedRow = row := by
    simpa using hobservedRow
  subst observedRow
  apply Prod.ext
  · funext probe
    exact hfun probe
  · exact hbit

theorem v13RealLinearNoTargetRowShear_bridgeTranscripts_of_row_matches
    {m : Nat} (i₀ : Fin m) (hm : 1 < m)
    (restX activeX bridgeX : F2Vec m)
    (activeA bridgeA : V13F2LinearEquiv m)
    (restRow activeRow : Fin m)
    (hrestFun :
      ∀ probe : F2Vec m,
        (v13RealLinearNoTargetRowShear i₀ hm).toEquiv probe restRow =
          bridgeA.toEquiv probe restRow)
    (hrestBit :
      (v13RealLinearNoTargetRowShear i₀ hm).toEquiv restX restRow =
        bridgeA.toEquiv bridgeX restRow)
    (hactiveFun :
      ∀ probe : F2Vec m,
        activeA.toEquiv probe activeRow = bridgeA.toEquiv probe activeRow)
    (hactiveBit :
      activeA.toEquiv activeX activeRow =
        bridgeA.toEquiv bridgeX activeRow) :
    v13RealLinearRowsTranscript ({restRow} : Finset (Fin m))
        (v13RealLinearPublicInput
          ({ x := restX, A := v13RealLinearNoTargetRowShear i₀ hm } :
            V13RealLinearWorld m)) =
      v13RealLinearRowsTranscript ({restRow} : Finset (Fin m))
        (v13RealLinearPublicInput
          ({ x := bridgeX, A := bridgeA } : V13RealLinearWorld m)) ∧
    v13RealLinearRowsTranscript ({activeRow} : Finset (Fin m))
        (v13RealLinearPublicInput
          ({ x := activeX, A := activeA } : V13RealLinearWorld m)) =
      v13RealLinearRowsTranscript ({activeRow} : Finset (Fin m))
        (v13RealLinearPublicInput
          ({ x := bridgeX, A := bridgeA } : V13RealLinearWorld m)) := by
  constructor
  · exact
      v13RealLinearRowsTranscript_singleton_eq_of_row_match
        (v13RealLinearNoTargetRowShear i₀ hm) bridgeA restX bridgeX
        restRow hrestFun hrestBit
  · exact
      v13RealLinearRowsTranscript_singleton_eq_of_row_match
        activeA bridgeA activeX bridgeX activeRow hactiveFun hactiveBit

theorem v13RealLinearZeroAtShearSum_singleBit
    {m : Nat} {i₀ spare : Fin m} (hne : spare ≠ i₀)
    (w : F2Vec m) :
    v13RealLinearZeroAtShearSum i₀
        (⟨v13RealLinearSingleBit spare, by
          have hne' : i₀ ≠ spare := fun h => hne h.symm
          simp [v13RealLinearSingleBit, hne']⟩ :
          V13RealLinearZeroAt i₀) w =
      w spare := by
  classical
  let s : V13RealLinearZeroAt i₀ :=
    ⟨v13RealLinearSingleBit spare, by
      have hne' : i₀ ≠ spare := fun h => hne h.symm
      simp [v13RealLinearSingleBit, hne']⟩
  unfold v13RealLinearZeroAtShearSum
  change (Finset.univ.erase i₀).sum (fun j => s.val j * w j) = w spare
  calc
    (Finset.univ.erase i₀).sum (fun j => s.val j * w j) =
        s.val spare * w spare := by
      refine Finset.sum_eq_single spare ?_ ?_
      · intro j _hj hjne
        simp [s, v13RealLinearSingleBit, hjne]
      · intro hnotMem
        simp [hne] at hnotMem
    _ = w spare := by
      simp [s, v13RealLinearSingleBit]

theorem v13RealLinearNoTargetRowShear_exists_bridgeX_for_row_target_bits
    {m : Nat} (i₀ : Fin m) (hm : 1 < m) (restRow : Fin m)
    (restBit targetBit : ZMod 2) :
    ∃ bridgeX : F2Vec m,
      (v13RealLinearNoTargetRowShear i₀ hm).toEquiv bridgeX restRow =
        restBit ∧
      bridgeX i₀ = targetBit := by
  classical
  by_cases hrow : restRow = i₀
  · subst restRow
    let spare := v13FinSpare i₀ hm
    let bridgeX : F2Vec m :=
      fun j => if j = i₀ then targetBit
        else if j = spare then restBit + targetBit else 0
    refine ⟨bridgeX, ?_, ?_⟩
    · have hspare : spare ≠ i₀ := by
        simpa [spare] using v13FinSpare_ne i₀ hm
      have hsum :
          v13RealLinearZeroAtShearSum i₀
              (⟨v13RealLinearSingleBit spare, by
                have hne' : i₀ ≠ spare := fun h => hspare h.symm
                simp [v13RealLinearSingleBit, hne']⟩ :
                V13RealLinearZeroAt i₀) bridgeX =
            restBit + targetBit := by
        rw [v13RealLinearZeroAtShearSum_singleBit hspare]
        simp [bridgeX, hspare]
      calc
        (v13RealLinearNoTargetRowShear i₀ hm).toEquiv bridgeX i₀ =
            targetBit + (restBit + targetBit) := by
          simp [v13RealLinearNoTargetRowShear,
            v13RealLinearZeroAtRowShear, bridgeX, spare, hsum]
        _ = restBit + targetBit + targetBit := by ring
        _ = restBit := f2_add_right_self restBit targetBit
    · simp [bridgeX]
  · let bridgeX : F2Vec m :=
      fun j => if j = i₀ then targetBit else if j = restRow then restBit else 0
    refine ⟨bridgeX, ?_, ?_⟩
    · simp [v13RealLinearNoTargetRowShear, v13RealLinearZeroAtRowShear,
        bridgeX, hrow]
    · simp [bridgeX]

def v13RealLinearNoTargetHardBridgeMap {m : Nat}
    (i₀ : Fin m) (hm : 1 < m) (activeRow : Fin m)
    (hactive : activeRow ≠ i₀) : V13F2LinearEquiv m :=
  let τ : Equiv.Perm (Fin m) :=
    (Equiv.swap activeRow i₀).trans
      (Equiv.swap activeRow (v13FinSpare i₀ hm))
  let P : V13F2LinearEquiv m := v13RealLinearPerm τ.symm
  let K : V13F2LinearEquiv m :=
    v13RealLinearZeroAtRowShear i₀
      ⟨v13RealLinearSingleBit activeRow, by
        have hne : i₀ ≠ activeRow := fun h => hactive h.symm
        simp [v13RealLinearSingleBit, hne]⟩
  v13RealLinearComp K P

theorem v13RealLinearNoTargetHardBridgeMap_activeRow
    {m : Nat} (i₀ : Fin m) (hm : 1 < m) (activeRow : Fin m)
    (hactive : activeRow ≠ i₀) (w : F2Vec m) :
    (v13RealLinearNoTargetHardBridgeMap i₀ hm activeRow hactive).toEquiv
        w activeRow =
      w i₀ := by
  have hiActive : i₀ ≠ activeRow := fun h => hactive h.symm
  have hiSpare : i₀ ≠ v13FinSpare i₀ hm :=
    fun h => v13FinSpare_ne i₀ hm h.symm
  simp [v13RealLinearNoTargetHardBridgeMap, v13RealLinearComp,
    v13RealLinearPerm, v13RealLinearZeroAtRowShear,
    v13RealLinearZeroAtShearSum_singleBit, hactive, hiActive, hiSpare,
    Equiv.swap_apply_def]

theorem v13RealLinearNoTargetHardBridgeMap_targetRow
    {m : Nat} (i₀ : Fin m) (hm : 1 < m) (activeRow : Fin m)
    (hactive : activeRow ≠ i₀) (w : F2Vec m) :
    (v13RealLinearNoTargetHardBridgeMap i₀ hm activeRow hactive).toEquiv
        w i₀ =
      (v13RealLinearNoTargetRowShear i₀ hm).toEquiv w i₀ := by
  classical
  let spare := v13FinSpare i₀ hm
  have hspare : spare ≠ i₀ := by
    simpa [spare] using v13FinSpare_ne i₀ hm
  have hsum :
      v13RealLinearZeroAtShearSum i₀
          (⟨v13RealLinearSingleBit spare, by
            have hne' : i₀ ≠ spare := fun h => hspare h.symm
            simp [v13RealLinearSingleBit, hne']⟩ :
            V13RealLinearZeroAt i₀) w =
        w spare := by
    exact v13RealLinearZeroAtShearSum_singleBit hspare w
  have hiActive : i₀ ≠ activeRow := fun h => hactive h.symm
  have hiSpare : i₀ ≠ v13FinSpare i₀ hm :=
    fun h => v13FinSpare_ne i₀ hm h.symm
  simp [v13RealLinearNoTargetHardBridgeMap, v13RealLinearNoTargetRowShear,
    v13RealLinearComp, v13RealLinearPerm, v13RealLinearZeroAtRowShear,
    v13RealLinearZeroAtShearSum_singleBit, hactive, hiActive, hiSpare,
    spare, hsum, Equiv.swap_apply_def]
  ring

theorem v13RealLinearNoTargetRowShear_exists_bridgeMap_for_rows
    {m : Nat} (i₀ : Fin m) (hm : 1 < m)
    (restRow activeRow : Fin m) (hneq : activeRow ≠ restRow) :
    ∃ bridgeA : V13F2LinearEquiv m,
      (∀ probe : F2Vec m,
        (v13RealLinearNoTargetRowShear i₀ hm).toEquiv probe restRow =
          bridgeA.toEquiv probe restRow) ∧
      (∀ probe : F2Vec m,
        bridgeA.toEquiv probe activeRow = probe i₀) := by
  classical
  by_cases hrest : restRow = i₀
  · subst restRow
    have hactive : activeRow ≠ i₀ := hneq
    refine
      ⟨v13RealLinearNoTargetHardBridgeMap i₀ hm activeRow hactive, ?_, ?_⟩
    · intro probe
      exact
        (v13RealLinearNoTargetHardBridgeMap_targetRow
          i₀ hm activeRow hactive probe).symm
    · intro probe
      exact
        v13RealLinearNoTargetHardBridgeMap_activeRow
          i₀ hm activeRow hactive probe
  · by_cases hactive : activeRow = i₀
    · subst activeRow
      refine ⟨v13RealLinearIdentity m, ?_, ?_⟩
      · intro probe
        simp [v13RealLinearNoTargetRowShear, v13RealLinearZeroAtRowShear,
          v13RealLinearIdentity, hrest]
      · intro probe
        simp [v13RealLinearIdentity]
    · refine
        ⟨v13RealLinearPerm (Equiv.swap activeRow i₀), ?_, ?_⟩
      · intro probe
        have hrestActive : restRow ≠ activeRow := fun h => hneq h.symm
        simp [v13RealLinearNoTargetRowShear, v13RealLinearZeroAtRowShear,
          v13RealLinearPerm, hrest, hrestActive, Equiv.swap_apply_def]
      · intro probe
        simp [v13RealLinearPerm, Equiv.swap_apply_def]

noncomputable def v13RealLinearFixedTargetRowOccurrenceZeroAtEmbedding
    {m : Nat} (row i₀ : Fin m) :
    V13RealLinearUniformFixedTargetRowOccurrence row i₀ ×
        V13RealLinearZeroAt i₀ ↪
      V13F2LinearEquiv m where
  toFun pair :=
    v13RealLinearComp pair.1.val
      (v13RealLinearZeroAtRowShear i₀ pair.2)
  inj' := by
    classical
    intro pair₀ pair₁ hmap
    rcases pair₀ with ⟨A₀, s₀⟩
    rcases pair₁ with ⟨A₁, s₁⟩
    have htarget₀ :
        ∀ w : F2Vec m, A₀.val.toEquiv w row = w i₀ :=
      (v13RealLinear_mem_targetRows_iff A₀.val i₀ row).1 A₀.property
    have htarget₁ :
        ∀ w : F2Vec m, A₁.val.toEquiv w row = w i₀ :=
      (v13RealLinear_mem_targetRows_iff A₁.val i₀ row).1 A₁.property
    have hs : s₀ = s₁ := by
      apply Subtype.ext
      funext j
      by_cases hj : j = i₀
      · subst j
        rw [s₀.property, s₁.property]
      · have hcoord :=
          congrFun
            (congrArg (fun A : V13F2LinearEquiv m =>
              A.toEquiv (v13RealLinearSingleBit j)) hmap) row
        simpa [v13RealLinearComp, htarget₀, htarget₁,
          v13RealLinearZeroAtRowShear_row_apply_singleBit_of_ne
            s₀ hj,
          v13RealLinearZeroAtRowShear_row_apply_singleBit_of_ne
            s₁ hj] using hcoord
    subst s₁
    have hA : A₀ = A₁ := by
      apply Subtype.ext
      apply v13RealLinearEquiv_ext
      intro x
      let K := v13RealLinearZeroAtRowShear i₀ s₀
      have hcoord :=
        congrArg (fun A : V13F2LinearEquiv m =>
          A.toEquiv (K.toEquiv.symm x)) hmap
      simpa [v13RealLinearComp, K] using hcoord
    subst A₁
    rfl

theorem v13RealLinearFixedTargetRowOccurrence_mul_zeroAt_card_le
    {m : Nat} (row i₀ : Fin m) :
    Fintype.card (V13RealLinearUniformFixedTargetRowOccurrence row i₀) *
        Fintype.card (V13RealLinearZeroAt i₀) ≤
      Fintype.card (V13F2LinearEquiv m) := by
  classical
  simpa [Fintype.card_prod] using
    Fintype.card_le_of_embedding
      (v13RealLinearFixedTargetRowOccurrenceZeroAtEmbedding row i₀)

theorem v13RealLinearFixedTargetRowOccurrence_counting
    {m : Nat} (row i₀ : Fin m) :
    Fintype.card (V13RealLinearUniformFixedTargetRowOccurrence row i₀) *
        2 ^ m ≤
      2 * Fintype.card (V13F2LinearEquiv m) := by
  classical
  let O := Fintype.card (V13RealLinearUniformFixedTargetRowOccurrence row i₀)
  let Z := Fintype.card (V13RealLinearZeroAt i₀)
  let A := Fintype.card (V13F2LinearEquiv m)
  have hOZ : O * Z ≤ A := by
    simpa [O, Z, A] using
      v13RealLinearFixedTargetRowOccurrence_mul_zeroAt_card_le row i₀
  have hZ : Z * 2 = 2 ^ m := by
    simpa [Z] using v13RealLinear_zeroAt_card_mul_two i₀
  calc
    O * 2 ^ m = O * (Z * 2) := by rw [hZ]
    _ = 2 * (O * Z) := by ring
    _ ≤ 2 * A := by exact Nat.mul_le_mul_left 2 hOZ

theorem v13RealLinearFixedTargetRowBitCylinder_card_le_equiv
    {m : Nat} (row i₀ : Fin m) (bit : ZMod 2) :
    Fintype.card
        (V13RealLinearUniformFixedTargetRowBitCylinder row i₀ bit) ≤
      Fintype.card (V13F2LinearEquiv m) := by
  classical
  let C :=
    Fintype.card
      (V13RealLinearUniformFixedTargetRowBitCylinder row i₀ bit)
  let O := Fintype.card (V13RealLinearUniformFixedTargetRowOccurrence row i₀)
  let B := Fintype.card (V13RealLinearBitAt i₀ bit)
  let A := Fintype.card (V13F2LinearEquiv m)
  have hC : C = O * B := by
    simpa [C, O, B] using
      v13RealLinearFixedTargetRowBitCylinder_card_eq row i₀ bit
  have hO : O * 2 ^ m ≤ 2 * A := by
    simpa [O, A] using
      v13RealLinearFixedTargetRowOccurrence_counting row i₀
  have hB : B * 2 = 2 ^ m := by
    simpa [B] using v13RealLinear_bitAt_card_mul_two i₀ bit
  have hdouble : 2 * C ≤ 2 * A := by
    rw [hC]
    calc
      2 * (O * B) = O * (B * 2) := by ring
      _ = O * 2 ^ m := by rw [hB]
      _ ≤ 2 * A := hO
  omega

theorem v13RealLinearFixedTargetRowBitCylinder_counting
    {m : Nat} (row i₀ : Fin m) (bit : ZMod 2) :
    Fintype.card
        (V13RealLinearUniformFixedTargetRowBitCylinder row i₀ bit) *
        2 ^ m ≤
      Fintype.card
        (V13RealLinearAdaptiveQRowWorld m (V13F2LinearEquiv m)) := by
  classical
  let C :=
    Fintype.card
      (V13RealLinearUniformFixedTargetRowBitCylinder row i₀ bit)
  let A := Fintype.card (V13F2LinearEquiv m)
  let X := 2 ^ m
  have hC : C ≤ A := by
    simpa [C, A] using
      v13RealLinearFixedTargetRowBitCylinder_card_le_equiv row i₀ bit
  have hworld :
      Fintype.card
          (V13RealLinearAdaptiveQRowWorld m (V13F2LinearEquiv m)) =
        A * X := by
    dsimp [V13RealLinearAdaptiveQRowWorld, A, X]
    rw [Fintype.card_prod]
    simp [F2Vec]
  calc
    C * X ≤ A * X := Nat.mul_le_mul_right X hC
    _ =
        Fintype.card
          (V13RealLinearAdaptiveQRowWorld m (V13F2LinearEquiv m)) := hworld.symm

noncomputable def v13RealLinearFixedTargetRowOccurrenceSwapEquiv
    {m : Nat} (row row' i₀ i₀' : Fin m) :
    V13RealLinearUniformFixedTargetRowOccurrence row i₀ ≃
      V13RealLinearUniformFixedTargetRowOccurrence row' i₀' where
  toFun A := by
    let ρ : Equiv.Perm (Fin m) := Equiv.swap row row'
    let κ : Equiv.Perm (Fin m) := Equiv.swap i₀ i₀'
    refine
      ⟨v13RealLinearComp (v13RealLinearPerm ρ)
        (v13RealLinearComp A.val (v13RealLinearPerm κ)), ?_⟩
    have htarget :
        ∀ w : F2Vec m, A.val.toEquiv w row = w i₀ :=
      (v13RealLinear_mem_targetRows_iff A.val i₀ row).1 A.property
    exact
      (v13RealLinear_mem_targetRows_iff
        (v13RealLinearComp (v13RealLinearPerm ρ)
          (v13RealLinearComp A.val (v13RealLinearPerm κ)))
        i₀' row').2 (by
          intro w
          simpa [ρ, κ, v13RealLinearComp, v13RealLinearPerm] using
            htarget ((v13RealLinearPerm κ).toEquiv w))
  invFun A := by
    let ρ : Equiv.Perm (Fin m) := Equiv.swap row row'
    let κ : Equiv.Perm (Fin m) := Equiv.swap i₀ i₀'
    refine
      ⟨v13RealLinearComp (v13RealLinearPerm ρ)
        (v13RealLinearComp A.val (v13RealLinearPerm κ)), ?_⟩
    have htarget :
        ∀ w : F2Vec m, A.val.toEquiv w row' = w i₀' :=
      (v13RealLinear_mem_targetRows_iff A.val i₀' row').1 A.property
    exact
      (v13RealLinear_mem_targetRows_iff
        (v13RealLinearComp (v13RealLinearPerm ρ)
          (v13RealLinearComp A.val (v13RealLinearPerm κ)))
        i₀ row).2 (by
          intro w
          simpa [ρ, κ, v13RealLinearComp, v13RealLinearPerm] using
            htarget ((v13RealLinearPerm κ).toEquiv w))
  left_inv A := by
    apply Subtype.ext
    apply v13RealLinearEquiv_ext
    intro x
    funext r
    simp [v13RealLinearComp, v13RealLinearPerm]
  right_inv A := by
    apply Subtype.ext
    apply v13RealLinearEquiv_ext
    intro x
    funext r
    simp [v13RealLinearComp, v13RealLinearPerm]

noncomputable instance {m : Nat} (i₀ : Fin m) :
    Fintype (V13RealLinearUniformTargetRowOccurrence i₀) := by
  classical
  unfold V13RealLinearUniformTargetRowOccurrence
  infer_instance

theorem v13RealLinearFixedTargetRowOccurrence_card_eq_of_swap
    {m : Nat} (row row' i₀ i₀' : Fin m) :
    Fintype.card (V13RealLinearUniformFixedTargetRowOccurrence row i₀) =
      Fintype.card (V13RealLinearUniformFixedTargetRowOccurrence row' i₀') := by
  classical
  exact
    Fintype.card_congr
      (v13RealLinearFixedTargetRowOccurrenceSwapEquiv
        row row' i₀ i₀')

noncomputable def v13RealLinearUniformTargetRowOccurrenceMass {m : Nat}
    (i₀ : Fin m) : Rat :=
  (Fintype.card (V13RealLinearUniformTargetRowOccurrence i₀) : Rat) /
    (Fintype.card (V13F2LinearEquiv m) : Rat)

def v13RealLinearShear01 : V13F2LinearEquiv 2 where
  toEquiv :=
    { toFun := fun x r => if r = 0 then x 0 else x 0 + x 1
      invFun := fun x r => if r = 0 then x 0 else x 0 + x 1
      left_inv := by
        intro x
        funext r
        fin_cases r
        · simp
        · simp
          calc
            x 0 + (x 0 + x 1) = x 1 + x 0 + x 0 := by ac_rfl
            _ = x 1 := f2_add_right_self (x 1) (x 0)
      right_inv := by
        intro x
        funext r
        fin_cases r
        · simp
        · simp
          calc
            x 0 + (x 0 + x 1) = x 1 + x 0 + x 0 := by ac_rfl
            _ = x 1 := f2_add_right_self (x 1) (x 0) }
  map_add := by
    intro x y
    funext r
    fin_cases r <;>
      simp [f2AddVec, add_assoc, add_left_comm, add_comm]
  map_zero := by
    funext r
    fin_cases r <;> simp [f2ZeroVec]

def v13RealLinearShear10 : V13F2LinearEquiv 2 where
  toEquiv :=
    { toFun := fun x r => if r = 0 then x 0 + x 1 else x 1
      invFun := fun x r => if r = 0 then x 0 + x 1 else x 1
      left_inv := by
        intro x
        funext r
        fin_cases r
        · simpa using f2_add_right_self (x 0) (x 1)
        · simp
      right_inv := by
        intro x
        funext r
        fin_cases r
        · simpa using f2_add_right_self (x 0) (x 1)
        · simp }
  map_add := by
    intro x y
    funext r
    fin_cases r <;>
      simp [f2AddVec, add_assoc, add_left_comm, add_comm]
  map_zero := by
    funext r
    fin_cases r <;> simp [f2ZeroVec]

def v13RealLinearShear01Swap : V13F2LinearEquiv 2 where
  toEquiv :=
    { toFun := fun x r => if r = 0 then x 0 + x 1 else x 0
      invFun := fun x r => if r = 0 then x 1 else x 0 + x 1
      left_inv := by
        intro x
        funext r
        fin_cases r
        · simp
        · simp
          calc
            (x 0 + x 1) + x 0 = x 1 + x 0 + x 0 := by ac_rfl
            _ = x 1 := f2_add_right_self (x 1) (x 0)
      right_inv := by
        intro x
        funext r
        fin_cases r
        · calc
            x 1 + (x 0 + x 1) = x 0 + x 1 + x 1 := by ac_rfl
            _ = x 0 := f2_add_right_self (x 0) (x 1)
        · simp }
  map_add := by
    intro x y
    funext r
    fin_cases r <;>
      simp [f2AddVec, add_assoc, add_left_comm, add_comm]
  map_zero := by
    funext r
    fin_cases r <;> simp [f2ZeroVec]

def v13RealLinearSwapShear10 : V13F2LinearEquiv 2 where
  toEquiv :=
    { toFun := fun x r => if r = 0 then x 1 else x 0 + x 1
      invFun := fun x r => if r = 0 then x 0 + x 1 else x 0
      left_inv := by
        intro x
        funext r
        fin_cases r
        · simp
          calc
            x 1 + (x 0 + x 1) = x 0 + x 1 + x 1 := by ac_rfl
            _ = x 0 := f2_add_right_self (x 0) (x 1)
        · simp
      right_inv := by
        intro x
        funext r
        fin_cases r
        · simp
        · simp
          calc
            (x 0 + x 1) + x 0 = x 1 + x 0 + x 0 := by ac_rfl
            _ = x 1 := f2_add_right_self (x 1) (x 0) }
  map_add := by
    intro x y
    funext r
    fin_cases r <;>
      simp [f2AddVec, add_assoc, add_left_comm, add_comm]
  map_zero := by
    funext r
    fin_cases r <;> simp [f2ZeroVec]

theorem v13RealLinearIdentity_targetRows_zero_nonempty :
    (V13RealLinearTargetRows (v13RealLinearIdentity 2) (0 : Fin 2)).Nonempty := by
  refine ⟨0, ?_⟩
  exact
    (v13RealLinear_mem_targetRows_iff
      (v13RealLinearIdentity 2) (0 : Fin 2) 0).2 (by
        intro w
        simp [v13RealLinearIdentity])

theorem v13RealLinearSwap_targetRows_zero_nonempty :
    (V13RealLinearTargetRows
      (v13RealLinearPerm (Equiv.swap (0 : Fin 2) (1 : Fin 2)))
      (0 : Fin 2)).Nonempty := by
  refine ⟨1, ?_⟩
  exact
    (v13RealLinear_mem_targetRows_iff
      (v13RealLinearPerm (Equiv.swap (0 : Fin 2) (1 : Fin 2)))
      (0 : Fin 2) 1).2 (by
        intro w
        simp [v13RealLinearPerm])

theorem v13RealLinearShear01_targetRows_zero_nonempty :
    (V13RealLinearTargetRows v13RealLinearShear01 (0 : Fin 2)).Nonempty := by
  refine ⟨0, ?_⟩
  exact
    (v13RealLinear_mem_targetRows_iff
      v13RealLinearShear01 (0 : Fin 2) 0).2 (by
        intro w
        simp [v13RealLinearShear01])

theorem v13RealLinearShear01Swap_targetRows_zero_nonempty :
    (V13RealLinearTargetRows v13RealLinearShear01Swap (0 : Fin 2)).Nonempty := by
  refine ⟨1, ?_⟩
  exact
    (v13RealLinear_mem_targetRows_iff
      v13RealLinearShear01Swap (0 : Fin 2) 1).2 (by
        intro w
        simp [v13RealLinearShear01Swap])

theorem v13RealLinearSwapShear10_targetRows_zero_empty :
    V13RealLinearTargetRows v13RealLinearSwapShear10 (0 : Fin 2) = ∅ := by
  classical
  ext row
  constructor
  · intro hrow
    have htarget :
        ∀ w : F2Vec 2,
          v13RealLinearSwapShear10.toEquiv w row = w (0 : Fin 2) :=
      (v13RealLinear_mem_targetRows_iff
        v13RealLinearSwapShear10 (0 : Fin 2) row).1 hrow
    fin_cases row
    · have h := htarget (v13RealLinearSingleBit (1 : Fin 2))
      norm_num [v13RealLinearSwapShear10, v13RealLinearSingleBit] at h
    · have h := htarget (v13RealLinearSingleBit (1 : Fin 2))
      norm_num [v13RealLinearSwapShear10, v13RealLinearSingleBit] at h
  · intro h
    simp at h

theorem v13RealLinearShear01_targetRows_one_empty :
    V13RealLinearTargetRows v13RealLinearShear01 (1 : Fin 2) = ∅ := by
  classical
  ext row
  constructor
  · intro hrow
    have htarget :
        ∀ w : F2Vec 2,
          v13RealLinearShear01.toEquiv w row = w (1 : Fin 2) :=
      (v13RealLinear_mem_targetRows_iff
        v13RealLinearShear01 (1 : Fin 2) row).1 hrow
    fin_cases row
    · have h := htarget (v13RealLinearSingleBit (1 : Fin 2))
      norm_num [v13RealLinearShear01, v13RealLinearSingleBit] at h
    · have h := htarget (v13RealLinearSingleBit (0 : Fin 2))
      norm_num [v13RealLinearShear01, v13RealLinearSingleBit] at h
  · intro h
    simp at h

theorem v13RealLinear_fin2_rows_card_le_one_cases
    (rows : Finset (Fin 2)) (hcard : rows.card ≤ 1) :
    rows = ∅ ∨
      rows = ({(0 : Fin 2)} : Finset (Fin 2)) ∨
        rows = ({(1 : Fin 2)} : Finset (Fin 2)) := by
  classical
  by_cases h0 : (0 : Fin 2) ∈ rows
  · by_cases h1 : (1 : Fin 2) ∈ rows
    · have htwo : 2 ≤ rows.card := by
        have hsub : ({(0 : Fin 2), (1 : Fin 2)} : Finset (Fin 2)) ⊆ rows := by
          intro row hrow
          fin_cases row <;> simp [h0, h1]
        simpa using
          Finset.card_le_card hsub
      omega
    · right
      left
      ext row
      fin_cases row <;> simp [h0, h1]
  · by_cases h1 : (1 : Fin 2) ∈ rows
    · right
      right
      ext row
      fin_cases row <;> simp [h0, h1]
    · left
      ext row
      fin_cases row <;> simp [h0, h1]

theorem v13RealLinearSwapShear10_not_generated_one_budget
    (observer : V13RealLinearCausalRowObserver 2 1) (x : F2Vec 2) :
    ¬ (v13RealLinearUniformCausalQRowExperiment observer).generated
        (0 : Fin 2) (v13RealLinearSwapShear10, x) := by
  exact
    (v13RealLinearUniformCausalQRowExperiment observer).not_generated_of_targetRows_empty
      (0 : Fin 2) (v13RealLinearSwapShear10, x)
      v13RealLinearSwapShear10_targetRows_zero_empty

theorem v13RealLinearShear01_not_generated_one_budget_one
    (observer : V13RealLinearCausalRowObserver 2 1) (x : F2Vec 2) :
    ¬ (v13RealLinearUniformCausalQRowExperiment observer).generated
        (1 : Fin 2) (v13RealLinearShear01, x) := by
  exact
    (v13RealLinearUniformCausalQRowExperiment observer).not_generated_of_targetRows_empty
      (1 : Fin 2) (v13RealLinearShear01, x)
      v13RealLinearShear01_targetRows_one_empty

theorem v13RealLinearSwapShear10_branchRows_cases
    (observer : V13RealLinearCausalRowObserver 2 1) (x : F2Vec 2) :
    (v13RealLinearUniformCausalQRowExperiment observer).branchRows
        (v13RealLinearSwapShear10, x) = ∅ ∨
      (v13RealLinearUniformCausalQRowExperiment observer).branchRows
          (v13RealLinearSwapShear10, x) =
        ({(0 : Fin 2)} : Finset (Fin 2)) ∨
        (v13RealLinearUniformCausalQRowExperiment observer).branchRows
          (v13RealLinearSwapShear10, x) =
        ({(1 : Fin 2)} : Finset (Fin 2)) := by
  exact
    v13RealLinear_fin2_rows_card_le_one_cases
      ((v13RealLinearUniformCausalQRowExperiment observer).branchRows
        (v13RealLinearSwapShear10, x))
      ((v13RealLinearUniformCausalQRowExperiment observer).branchRows_card_le
        (v13RealLinearSwapShear10, x))

theorem v13RealLinearShear01_branchRows_cases
    (observer : V13RealLinearCausalRowObserver 2 1) (x : F2Vec 2) :
    (v13RealLinearUniformCausalQRowExperiment observer).branchRows
        (v13RealLinearShear01, x) = ∅ ∨
      (v13RealLinearUniformCausalQRowExperiment observer).branchRows
          (v13RealLinearShear01, x) =
        ({(0 : Fin 2)} : Finset (Fin 2)) ∨
        (v13RealLinearUniformCausalQRowExperiment observer).branchRows
          (v13RealLinearShear01, x) =
        ({(1 : Fin 2)} : Finset (Fin 2)) := by
  exact
    v13RealLinear_fin2_rows_card_le_one_cases
      ((v13RealLinearUniformCausalQRowExperiment observer).branchRows
        (v13RealLinearShear01, x))
      ((v13RealLinearUniformCausalQRowExperiment observer).branchRows_card_le
        (v13RealLinearShear01, x))

theorem v13RealLinearSwapShear10_branchRows_ne_empty_of_singletonWitness
    (observer : V13RealLinearCausalRowObserver 2 1) (x : F2Vec 2)
    (omega : V13RealLinearAdaptiveQRowWorld 2 (V13F2LinearEquiv 2))
    (row : Fin 2)
    (homegaRows :
      (v13RealLinearUniformCausalQRowExperiment observer).branchRows omega =
        ({row} : Finset (Fin 2))) :
    (v13RealLinearUniformCausalQRowExperiment observer).branchRows
        (v13RealLinearSwapShear10, x) ≠ ∅ := by
  classical
  intro hrestRows
  let E := v13RealLinearUniformCausalQRowExperiment observer
  let rest : V13RealLinearAdaptiveQRowWorld 2 (V13F2LinearEquiv 2) :=
    (v13RealLinearSwapShear10, x)
  let publicRest :=
    v13RealLinearPublicInput (E.world rest)
  let publicOmega :=
    v13RealLinearPublicInput (E.world omega)
  have hobserverRestRows :
      observer.rows (observer.branch publicRest) = ∅ := by
    simpa [E, rest, publicRest, v13RealLinearUniformCausalQRowExperiment,
      v13RealLinearUniformQRowExperiment,
      V13RealLinearAdaptiveQRowExperiment.branchRows,
      V13RealLinearAdaptiveQRowExperiment.branch,
      V13RealLinearCausalRowObserver.toAdaptive,
      V13RealLinearCausalRowObserver.staticBranch] using hrestRows
  have hsame :
      v13RealLinearRowsTranscript
          (observer.rows (observer.branch publicRest)) publicRest =
        v13RealLinearRowsTranscript
          (observer.rows (observer.branch publicRest)) publicOmega := by
    funext row
    have hmemEmpty : row.val ∈ (∅ : Finset (Fin 2)) := by
      rw [← hobserverRestRows]
      exact row.property
    simp at hmemEmpty
  have hbranch :
      observer.branch publicOmega = observer.branch publicRest :=
    observer.branch_eq_of_same_branchRowsTranscript publicRest publicOmega
      hsame
  have hrowsEq :
      observer.rows (observer.branch publicOmega) =
        observer.rows (observer.branch publicRest) :=
    congrArg observer.rows hbranch
  have homegaObserverRows :
      observer.rows (observer.branch publicOmega) =
        ({row} : Finset (Fin 2)) := by
    simpa [E, publicOmega, v13RealLinearUniformCausalQRowExperiment,
      v13RealLinearUniformQRowExperiment,
      V13RealLinearAdaptiveQRowExperiment.branchRows,
      V13RealLinearAdaptiveQRowExperiment.branch,
      V13RealLinearCausalRowObserver.toAdaptive,
      V13RealLinearCausalRowObserver.staticBranch] using homegaRows
  have hsingletonEmpty :
      ({row} : Finset (Fin 2)) = ∅ := by
    rw [← homegaObserverRows, hrowsEq, hobserverRestRows]
  have hmem : row ∈ ({row} : Finset (Fin 2)) := by simp
  rw [hsingletonEmpty] at hmem
  simp at hmem

theorem v13RealLinearSwapShear10_branchRows_ne_zero_of_singletonOneWitness
    (observer : V13RealLinearCausalRowObserver 2 1) (x : F2Vec 2)
    (omega : V13RealLinearAdaptiveQRowWorld 2 (V13F2LinearEquiv 2))
    (homegaRows :
      (v13RealLinearUniformCausalQRowExperiment observer).branchRows omega =
        ({(1 : Fin 2)} : Finset (Fin 2)))
    (htarget :
      (1 : Fin 2) ∈ V13RealLinearTargetRows omega.1 (0 : Fin 2)) :
    (v13RealLinearUniformCausalQRowExperiment observer).branchRows
        (v13RealLinearSwapShear10, x) ≠
      ({(0 : Fin 2)} : Finset (Fin 2)) := by
  classical
  intro hrestRows
  let E := v13RealLinearUniformCausalQRowExperiment observer
  let rest : V13RealLinearAdaptiveQRowWorld 2 (V13F2LinearEquiv 2) :=
    (v13RealLinearSwapShear10, x)
  let bridgeX : F2Vec 2 :=
    fun r => if r = (0 : Fin 2) then omega.2 (0 : Fin 2) else x (1 : Fin 2)
  let bridge : V13RealLinearAdaptiveQRowWorld 2 (V13F2LinearEquiv 2) :=
    (v13RealLinearPerm (Equiv.swap (0 : Fin 2) (1 : Fin 2)), bridgeX)
  let publicRest := v13RealLinearPublicInput (E.world rest)
  let publicBridge := v13RealLinearPublicInput (E.world bridge)
  let publicOmega := v13RealLinearPublicInput (E.world omega)
  have hrestObserverRows :
      observer.rows (observer.branch publicRest) =
        ({(0 : Fin 2)} : Finset (Fin 2)) := by
    simpa [E, rest, publicRest, v13RealLinearUniformCausalQRowExperiment,
      v13RealLinearUniformQRowExperiment,
      V13RealLinearAdaptiveQRowExperiment.branchRows,
      V13RealLinearAdaptiveQRowExperiment.branch,
      V13RealLinearCausalRowObserver.toAdaptive,
      V13RealLinearCausalRowObserver.staticBranch] using hrestRows
  have hsameRest :
      v13RealLinearRowsTranscript
          (observer.rows (observer.branch publicRest)) publicRest =
        v13RealLinearRowsTranscript
          (observer.rows (observer.branch publicRest)) publicBridge := by
    rw [hrestObserverRows]
    funext row
    rcases row with ⟨row, hrow⟩
    have hrow0 : row = (0 : Fin 2) := by
      simpa using hrow
    subst row
    apply Prod.ext
    · funext probe
      change
        v13RealLinearSwapShear10.toEquiv probe (0 : Fin 2) =
          (v13RealLinearPerm (Equiv.swap (0 : Fin 2) (1 : Fin 2))).toEquiv
            probe (0 : Fin 2)
      simp [v13RealLinearSwapShear10, v13RealLinearPerm]
    · change
        v13RealLinearSwapShear10.toEquiv x (0 : Fin 2) =
          (v13RealLinearPerm (Equiv.swap (0 : Fin 2) (1 : Fin 2))).toEquiv
            bridgeX (0 : Fin 2)
      simp [v13RealLinearSwapShear10, v13RealLinearPerm, bridgeX]
  have hbranchRest :
      observer.branch publicBridge = observer.branch publicRest :=
    observer.branch_eq_of_same_branchRowsTranscript publicRest publicBridge
      hsameRest
  have hbridgeRowsZero :
      E.branchRows bridge = ({(0 : Fin 2)} : Finset (Fin 2)) := by
    have hrowsEq :
        observer.rows (observer.branch publicBridge) =
          observer.rows (observer.branch publicRest) :=
      congrArg observer.rows hbranchRest
    simpa [E, bridge, publicBridge, v13RealLinearUniformCausalQRowExperiment,
      v13RealLinearUniformQRowExperiment,
      V13RealLinearAdaptiveQRowExperiment.branchRows,
      V13RealLinearAdaptiveQRowExperiment.branch,
      V13RealLinearCausalRowObserver.toAdaptive,
      V13RealLinearCausalRowObserver.staticBranch] using
        hrowsEq.trans hrestObserverRows
  have homegaObserverRows :
      observer.rows (observer.branch publicOmega) =
        ({(1 : Fin 2)} : Finset (Fin 2)) := by
    simpa [E, publicOmega, v13RealLinearUniformCausalQRowExperiment,
      v13RealLinearUniformQRowExperiment,
      V13RealLinearAdaptiveQRowExperiment.branchRows,
      V13RealLinearAdaptiveQRowExperiment.branch,
      V13RealLinearCausalRowObserver.toAdaptive,
      V13RealLinearCausalRowObserver.staticBranch] using homegaRows
  have htargetFun :
      ∀ probe : F2Vec 2, omega.1.toEquiv probe (1 : Fin 2) =
        probe (0 : Fin 2) :=
    (v13RealLinear_mem_targetRows_iff omega.1 (0 : Fin 2) (1 : Fin 2)).1
      htarget
  have hsameOmega :
      v13RealLinearRowsTranscript
          (observer.rows (observer.branch publicOmega)) publicOmega =
        v13RealLinearRowsTranscript
          (observer.rows (observer.branch publicOmega)) publicBridge := by
    rw [homegaObserverRows]
    funext row
    rcases row with ⟨row, hrow⟩
    have hrow1 : row = (1 : Fin 2) := by
      simpa using hrow
    subst row
    apply Prod.ext
    · funext probe
      change
        omega.1.toEquiv probe (1 : Fin 2) =
          (v13RealLinearPerm (Equiv.swap (0 : Fin 2) (1 : Fin 2))).toEquiv
            probe (1 : Fin 2)
      rw [htargetFun probe]
      simp [v13RealLinearPerm]
    · have htargetX := htargetFun omega.2
      change
        omega.1.toEquiv omega.2 (1 : Fin 2) =
          (v13RealLinearPerm (Equiv.swap (0 : Fin 2) (1 : Fin 2))).toEquiv
            bridgeX (1 : Fin 2)
      rw [htargetX]
      simp [v13RealLinearPerm, bridgeX]
  have hbranchOmega :
      observer.branch publicBridge = observer.branch publicOmega :=
    observer.branch_eq_of_same_branchRowsTranscript publicOmega publicBridge
      hsameOmega
  have hbridgeRowsOne :
      E.branchRows bridge = ({(1 : Fin 2)} : Finset (Fin 2)) := by
    have hrowsEq :
        observer.rows (observer.branch publicBridge) =
          observer.rows (observer.branch publicOmega) :=
      congrArg observer.rows hbranchOmega
    simpa [E, bridge, publicBridge, v13RealLinearUniformCausalQRowExperiment,
      v13RealLinearUniformQRowExperiment,
      V13RealLinearAdaptiveQRowExperiment.branchRows,
      V13RealLinearAdaptiveQRowExperiment.branch,
      V13RealLinearCausalRowObserver.toAdaptive,
      V13RealLinearCausalRowObserver.staticBranch] using
        hrowsEq.trans homegaObserverRows
  have hzeroOne :
      ({(0 : Fin 2)} : Finset (Fin 2)) =
        ({(1 : Fin 2)} : Finset (Fin 2)) :=
    hbridgeRowsZero.symm.trans hbridgeRowsOne
  have hmem : (0 : Fin 2) ∈ ({(1 : Fin 2)} : Finset (Fin 2)) := by
    rw [← hzeroOne]
    simp
  simp at hmem

theorem v13RealLinearSwapShear10_branchRows_ne_one_of_singletonZeroWitness
    (observer : V13RealLinearCausalRowObserver 2 1) (x : F2Vec 2)
    (omega : V13RealLinearAdaptiveQRowWorld 2 (V13F2LinearEquiv 2))
    (homegaRows :
      (v13RealLinearUniformCausalQRowExperiment observer).branchRows omega =
        ({(0 : Fin 2)} : Finset (Fin 2)))
    (htarget :
      (0 : Fin 2) ∈ V13RealLinearTargetRows omega.1 (0 : Fin 2)) :
    (v13RealLinearUniformCausalQRowExperiment observer).branchRows
        (v13RealLinearSwapShear10, x) ≠
      ({(1 : Fin 2)} : Finset (Fin 2)) := by
  classical
  intro hrestRows
  let E := v13RealLinearUniformCausalQRowExperiment observer
  let rest : V13RealLinearAdaptiveQRowWorld 2 (V13F2LinearEquiv 2) :=
    (v13RealLinearSwapShear10, x)
  let bridgeX : F2Vec 2 :=
    fun r =>
      if r = (0 : Fin 2) then omega.2 (0 : Fin 2)
      else omega.2 (0 : Fin 2) + (x (0 : Fin 2) + x (1 : Fin 2))
  let bridge : V13RealLinearAdaptiveQRowWorld 2 (V13F2LinearEquiv 2) :=
    (v13RealLinearShear01, bridgeX)
  let publicRest := v13RealLinearPublicInput (E.world rest)
  let publicBridge := v13RealLinearPublicInput (E.world bridge)
  let publicOmega := v13RealLinearPublicInput (E.world omega)
  have hrestObserverRows :
      observer.rows (observer.branch publicRest) =
        ({(1 : Fin 2)} : Finset (Fin 2)) := by
    simpa [E, rest, publicRest, v13RealLinearUniformCausalQRowExperiment,
      v13RealLinearUniformQRowExperiment,
      V13RealLinearAdaptiveQRowExperiment.branchRows,
      V13RealLinearAdaptiveQRowExperiment.branch,
      V13RealLinearCausalRowObserver.toAdaptive,
      V13RealLinearCausalRowObserver.staticBranch] using hrestRows
  have hsameRest :
      v13RealLinearRowsTranscript
          (observer.rows (observer.branch publicRest)) publicRest =
        v13RealLinearRowsTranscript
          (observer.rows (observer.branch publicRest)) publicBridge := by
    rw [hrestObserverRows]
    funext row
    rcases row with ⟨row, hrow⟩
    have hrow1 : row = (1 : Fin 2) := by
      simpa using hrow
    subst row
    apply Prod.ext
    · funext probe
      change
        v13RealLinearSwapShear10.toEquiv probe (1 : Fin 2) =
          v13RealLinearShear01.toEquiv probe (1 : Fin 2)
      simp [v13RealLinearSwapShear10, v13RealLinearShear01]
    · change
        v13RealLinearSwapShear10.toEquiv x (1 : Fin 2) =
          v13RealLinearShear01.toEquiv bridgeX (1 : Fin 2)
      simp [v13RealLinearSwapShear10, v13RealLinearShear01, bridgeX,
        add_assoc, add_left_comm, add_comm]
      simpa using f2_add_right_self (0 : ZMod 2) (omega.2 (0 : Fin 2))
  have hbranchRest :
      observer.branch publicBridge = observer.branch publicRest :=
    observer.branch_eq_of_same_branchRowsTranscript publicRest publicBridge
      hsameRest
  have hbridgeRowsOne :
      E.branchRows bridge = ({(1 : Fin 2)} : Finset (Fin 2)) := by
    have hrowsEq :
        observer.rows (observer.branch publicBridge) =
          observer.rows (observer.branch publicRest) :=
      congrArg observer.rows hbranchRest
    simpa [E, bridge, publicBridge, v13RealLinearUniformCausalQRowExperiment,
      v13RealLinearUniformQRowExperiment,
      V13RealLinearAdaptiveQRowExperiment.branchRows,
      V13RealLinearAdaptiveQRowExperiment.branch,
      V13RealLinearCausalRowObserver.toAdaptive,
      V13RealLinearCausalRowObserver.staticBranch] using
        hrowsEq.trans hrestObserverRows
  have homegaObserverRows :
      observer.rows (observer.branch publicOmega) =
        ({(0 : Fin 2)} : Finset (Fin 2)) := by
    simpa [E, publicOmega, v13RealLinearUniformCausalQRowExperiment,
      v13RealLinearUniformQRowExperiment,
      V13RealLinearAdaptiveQRowExperiment.branchRows,
      V13RealLinearAdaptiveQRowExperiment.branch,
      V13RealLinearCausalRowObserver.toAdaptive,
      V13RealLinearCausalRowObserver.staticBranch] using homegaRows
  have htargetFun :
      ∀ probe : F2Vec 2, omega.1.toEquiv probe (0 : Fin 2) =
        probe (0 : Fin 2) :=
    (v13RealLinear_mem_targetRows_iff omega.1 (0 : Fin 2) (0 : Fin 2)).1
      htarget
  have hsameOmega :
      v13RealLinearRowsTranscript
          (observer.rows (observer.branch publicOmega)) publicOmega =
        v13RealLinearRowsTranscript
          (observer.rows (observer.branch publicOmega)) publicBridge := by
    rw [homegaObserverRows]
    funext row
    rcases row with ⟨row, hrow⟩
    have hrow0 : row = (0 : Fin 2) := by
      simpa using hrow
    subst row
    apply Prod.ext
    · funext probe
      change
        omega.1.toEquiv probe (0 : Fin 2) =
          v13RealLinearShear01.toEquiv probe (0 : Fin 2)
      rw [htargetFun probe]
      simp [v13RealLinearShear01]
    · have htargetX := htargetFun omega.2
      change
        omega.1.toEquiv omega.2 (0 : Fin 2) =
          v13RealLinearShear01.toEquiv bridgeX (0 : Fin 2)
      rw [htargetX]
      simp [v13RealLinearShear01, bridgeX]
  have hbranchOmega :
      observer.branch publicBridge = observer.branch publicOmega :=
    observer.branch_eq_of_same_branchRowsTranscript publicOmega publicBridge
      hsameOmega
  have hbridgeRowsZero :
      E.branchRows bridge = ({(0 : Fin 2)} : Finset (Fin 2)) := by
    have hrowsEq :
        observer.rows (observer.branch publicBridge) =
          observer.rows (observer.branch publicOmega) :=
      congrArg observer.rows hbranchOmega
    simpa [E, bridge, publicBridge, v13RealLinearUniformCausalQRowExperiment,
      v13RealLinearUniformQRowExperiment,
      V13RealLinearAdaptiveQRowExperiment.branchRows,
      V13RealLinearAdaptiveQRowExperiment.branch,
      V13RealLinearCausalRowObserver.toAdaptive,
      V13RealLinearCausalRowObserver.staticBranch] using
        hrowsEq.trans homegaObserverRows
  have honeZero :
      ({(1 : Fin 2)} : Finset (Fin 2)) =
        ({(0 : Fin 2)} : Finset (Fin 2)) :=
    hbridgeRowsOne.symm.trans hbridgeRowsZero
  have hmem : (1 : Fin 2) ∈ ({(0 : Fin 2)} : Finset (Fin 2)) := by
    rw [← honeZero]
    simp
  simp at hmem

noncomputable def v13RealLinearTargetRowOccurrenceFour
    (k : Fin 4) : V13RealLinearUniformTargetRowOccurrence (0 : Fin 2) :=
  match k with
  | ⟨0, _⟩ =>
      ⟨v13RealLinearIdentity 2,
        v13RealLinearIdentity_targetRows_zero_nonempty⟩
  | ⟨1, _⟩ =>
      ⟨v13RealLinearPerm (Equiv.swap (0 : Fin 2) (1 : Fin 2)),
        v13RealLinearSwap_targetRows_zero_nonempty⟩
  | ⟨2, _⟩ =>
      ⟨v13RealLinearShear01,
        v13RealLinearShear01_targetRows_zero_nonempty⟩
  | ⟨3, _⟩ =>
      ⟨v13RealLinearShear01Swap,
        v13RealLinearShear01Swap_targetRows_zero_nonempty⟩
  | ⟨n + 4, h⟩ => by omega

theorem v13RealLinearTargetRowOccurrenceFour_injective :
    Function.Injective v13RealLinearTargetRowOccurrenceFour := by
  intro a b h
  fin_cases a <;> fin_cases b
  all_goals
    simp [v13RealLinearTargetRowOccurrenceFour, v13RealLinearIdentity,
      v13RealLinearPerm, v13RealLinearShear01, v13RealLinearShear01Swap] at h ⊢
  all_goals
    have hmatrix := congrArg
      (fun A : V13RealLinearUniformTargetRowOccurrence (0 : Fin 2) =>
        (A.val.toEquiv (v13RealLinearSingleBit (0 : Fin 2)) (0 : Fin 2),
          A.val.toEquiv (v13RealLinearSingleBit (0 : Fin 2)) (1 : Fin 2),
          A.val.toEquiv (v13RealLinearSingleBit (1 : Fin 2)) (0 : Fin 2),
          A.val.toEquiv (v13RealLinearSingleBit (1 : Fin 2)) (1 : Fin 2))) h
    norm_num [v13RealLinearIdentity, v13RealLinearPerm,
      v13RealLinearShear01, v13RealLinearShear01Swap,
      v13RealLinearSingleBit] at hmatrix

theorem v13RealLinearUniformTargetRowOccurrence_card_four_le :
    4 ≤
      Fintype.card (V13RealLinearUniformTargetRowOccurrence (0 : Fin 2)) := by
  classical
  exact
    Fintype.card_le_of_embedding
      { toFun := v13RealLinearTargetRowOccurrenceFour
        inj' := v13RealLinearTargetRowOccurrenceFour_injective }

theorem v13RealLinearUniformTargetRowOccurrenceMass_two_zero_gt_half
    (hcard : Fintype.card (V13F2LinearEquiv 2) ≤ 6) :
    (1 / 2 : Rat) <
      v13RealLinearUniformTargetRowOccurrenceMass (0 : Fin 2) := by
  classical
  unfold v13RealLinearUniformTargetRowOccurrenceMass
  let O := Fintype.card (V13RealLinearUniformTargetRowOccurrence (0 : Fin 2))
  let A := Fintype.card (V13F2LinearEquiv 2)
  have hO : (4 : Rat) ≤ (O : Rat) := by
    exact_mod_cast v13RealLinearUniformTargetRowOccurrence_card_four_le
  have hA : (A : Rat) ≤ 6 := by
    exact_mod_cast hcard
  have hAposNat : 0 < A := by
    dsimp [A]
    exact Fintype.card_pos_iff.mpr ⟨v13RealLinearIdentity 2⟩
  have hApos : (0 : Rat) < (A : Rat) := by
    exact_mod_cast hAposNat
  change (1 / 2 : Rat) < (O : Rat) / (A : Rat)
  rw [lt_div_iff₀ hApos]
  nlinarith

abbrev V13RealLinearNonzeroF2Vec2 :=
  {v : F2Vec 2 // v ≠ f2ZeroVec 2}

noncomputable instance : Fintype V13RealLinearNonzeroF2Vec2 := by
  unfold V13RealLinearNonzeroF2Vec2
  infer_instance

theorem v13RealLinearNonzeroF2Vec2_card :
    Fintype.card V13RealLinearNonzeroF2Vec2 = 3 := by
  unfold V13RealLinearNonzeroF2Vec2
  rw [Fintype.card_subtype_compl (fun v : F2Vec 2 => v = f2ZeroVec 2)]
  rw [Fintype.card_subtype_eq]
  norm_num [F2Vec]

theorem v13RealLinearNonzeroF2Vec2_ne_card_le_two
    (v : V13RealLinearNonzeroF2Vec2) :
    Fintype.card {w : V13RealLinearNonzeroF2Vec2 // w.val ≠ v.val} ≤ 2 := by
  rw [Fintype.card_subtype_compl
    (fun w : V13RealLinearNonzeroF2Vec2 => w.val = v.val)]
  have hcard :
      Fintype.card {w : V13RealLinearNonzeroF2Vec2 // w.val = v.val} = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨v, rfl⟩, ?_⟩
    intro y
    apply Subtype.ext
    apply Subtype.ext
    exact y.property
  rw [hcard]
  rw [v13RealLinearNonzeroF2Vec2_card]

lemma v13_zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have hlt : a.val < 2 := ZMod.val_lt a
  have hcases : a.val = 0 ∨ a.val = 1 := by omega
  rcases hcases with h | h
  · left
    rw [← ZMod.natCast_zmod_val a, h]
    norm_num
  · right
    rw [← ZMod.natCast_zmod_val a, h]
    norm_num

lemma v13RealLinear_f2vec2_cases (x : F2Vec 2) :
    x = f2ZeroVec 2 ∨
      x = v13RealLinearSingleBit (0 : Fin 2) ∨
      x = v13RealLinearSingleBit (1 : Fin 2) ∨
      x = f2AddVec (v13RealLinearSingleBit (0 : Fin 2))
        (v13RealLinearSingleBit (1 : Fin 2)) := by
  have hx0 : x 0 = 0 ∨ x 0 = 1 := v13_zmod2_cases (x 0)
  have hx1 : x 1 = 0 ∨ x 1 = 1 := v13_zmod2_cases (x 1)
  rcases hx0 with h00 | h01 <;> rcases hx1 with h10 | h11
  · left
    funext r
    fin_cases r <;> simp [f2ZeroVec, h00, h10]
  · right; right; left
    funext r
    fin_cases r <;> simp [v13RealLinearSingleBit, h00, h11]
  · right; left
    funext r
    fin_cases r <;> simp [v13RealLinearSingleBit, h01, h10]
  · right; right; right
    funext r
    fin_cases r <;> simp [v13RealLinearSingleBit, f2AddVec, h01, h11]

lemma v13RealLinear_f2vec2_eq_singleBit_one_of_ne_zero_of_coord_zero
    (x : F2Vec 2) (hne : x ≠ f2ZeroVec 2)
    (hcoord : x (0 : Fin 2) = 0) :
    x = v13RealLinearSingleBit (1 : Fin 2) := by
  rcases v13RealLinear_f2vec2_cases x with hx | hx | hx | hx
  · exact False.elim (hne hx)
  · subst x
    simp [v13RealLinearSingleBit] at hcoord
  · exact hx
  · subst x
    simp [v13RealLinearSingleBit, f2AddVec] at hcoord

lemma v13RealLinear_f2vec2_eq_singleBit_zero_of_ne_zero_of_coord_one_zero
    (x : F2Vec 2) (hne : x ≠ f2ZeroVec 2)
    (hcoord : x (1 : Fin 2) = 0) :
    x = v13RealLinearSingleBit (0 : Fin 2) := by
  rcases v13RealLinear_f2vec2_cases x with hx | hx | hx | hx
  · exact False.elim (hne hx)
  · exact hx
  · subst x
    simp [v13RealLinearSingleBit] at hcoord
  · subst x
    simp [v13RealLinearSingleBit, f2AddVec] at hcoord

theorem v13RealLinear_equiv_two_ext
    (A B : V13F2LinearEquiv 2)
    (h0 : A.toEquiv (v13RealLinearSingleBit (0 : Fin 2)) =
      B.toEquiv (v13RealLinearSingleBit (0 : Fin 2)))
    (h1 : A.toEquiv (v13RealLinearSingleBit (1 : Fin 2)) =
      B.toEquiv (v13RealLinearSingleBit (1 : Fin 2))) :
    A = B := by
  cases A with
  | mk Ae Aadd Azero =>
  cases B with
  | mk Be Badd Bzero =>
  have heq : Ae = Be := by
    apply Equiv.ext
    intro x
    rcases v13RealLinear_f2vec2_cases x with hx | hx | hx | hx
    · subst x
      simpa using Azero.trans Bzero.symm
    · subst x
      simpa using h0
    · subst x
      simpa using h1
    · subst x
      calc
        Ae (f2AddVec (v13RealLinearSingleBit (0 : Fin 2))
            (v13RealLinearSingleBit (1 : Fin 2))) =
          f2AddVec (Ae (v13RealLinearSingleBit (0 : Fin 2)))
            (Ae (v13RealLinearSingleBit (1 : Fin 2))) := Aadd _ _
        _ = f2AddVec (Be (v13RealLinearSingleBit (0 : Fin 2)))
            (Be (v13RealLinearSingleBit (1 : Fin 2))) := by rw [h0, h1]
        _ = Be (f2AddVec (v13RealLinearSingleBit (0 : Fin 2))
            (v13RealLinearSingleBit (1 : Fin 2))) := (Badd _ _).symm
  subst Be
  rfl

abbrev V13RealLinearTwoBasisImagePairs :=
  Sigma (fun v : V13RealLinearNonzeroF2Vec2 =>
    {w : V13RealLinearNonzeroF2Vec2 // w.val ≠ v.val})

noncomputable def v13RealLinearTwoBasisImagePair
    (A : V13F2LinearEquiv 2) : V13RealLinearTwoBasisImagePairs := by
  let e0 := v13RealLinearSingleBit (0 : Fin 2)
  let e1 := v13RealLinearSingleBit (1 : Fin 2)
  have hsymmZero : A.toEquiv.symm (f2ZeroVec 2) = f2ZeroVec 2 := by
    apply A.toEquiv.injective
    simp [A.map_zero]
  let v0 : V13RealLinearNonzeroF2Vec2 := ⟨A.toEquiv e0, by
    intro hzero
    have hpre := congrArg A.toEquiv.symm hzero
    have hne : e0 ≠ f2ZeroVec 2 := by
      intro h
      have hp := congrFun h (0 : Fin 2)
      simp [e0, v13RealLinearSingleBit, f2ZeroVec] at hp
    apply hne
    rw [hsymmZero] at hpre
    simpa [e0] using hpre⟩
  let v1 : V13RealLinearNonzeroF2Vec2 := ⟨A.toEquiv e1, by
    intro hzero
    have hpre := congrArg A.toEquiv.symm hzero
    have hne : e1 ≠ f2ZeroVec 2 := by
      intro h
      have hp := congrFun h (1 : Fin 2)
      simp [e1, v13RealLinearSingleBit, f2ZeroVec] at hp
    apply hne
    rw [hsymmZero] at hpre
    simpa [e1] using hpre⟩
  exact ⟨v0, ⟨v1, by
    intro heq
    have hpre := congrArg A.toEquiv.symm heq
    have hne : e1 ≠ e0 := by
      intro h
      have hp := congrFun h (0 : Fin 2)
      simp [e0, e1, v13RealLinearSingleBit] at hp
    apply hne
    simpa [v0, v1, e0, e1] using hpre⟩⟩

theorem v13RealLinearTwoBasisImagePair_injective :
    Function.Injective v13RealLinearTwoBasisImagePair := by
  intro A B h
  apply v13RealLinear_equiv_two_ext A B
  · exact congrArg Subtype.val (congrArg Sigma.fst h)
  · exact congrArg
      (fun p : V13RealLinearTwoBasisImagePairs => (p.2).val.val) h

theorem v13RealLinearTwoBasisImagePairs_card_le_six :
    Fintype.card V13RealLinearTwoBasisImagePairs ≤ 6 := by
  classical
  rw [Fintype.card_sigma]
  calc
    (∑ v : V13RealLinearNonzeroF2Vec2,
        Fintype.card {w : V13RealLinearNonzeroF2Vec2 // w.val ≠ v.val})
        ≤ ∑ _v : V13RealLinearNonzeroF2Vec2, 2 := by
      apply Finset.sum_le_sum
      intro v _hv
      exact v13RealLinearNonzeroF2Vec2_ne_card_le_two v
    _ = 6 := by
      rw [Finset.sum_const]
      rw [Finset.card_univ]
      rw [v13RealLinearNonzeroF2Vec2_card]
      norm_num

theorem v13RealLinear_f2_equiv_two_card_le_six :
    Fintype.card (V13F2LinearEquiv 2) ≤ 6 := by
  have hleImage : Fintype.card (V13F2LinearEquiv 2) ≤
      Fintype.card V13RealLinearTwoBasisImagePairs :=
    Fintype.card_le_of_embedding
      { toFun := v13RealLinearTwoBasisImagePair
        inj' := v13RealLinearTwoBasisImagePair_injective }
  exact hleImage.trans v13RealLinearTwoBasisImagePairs_card_le_six

theorem v13RealLinear_f2_equiv_two_card_four_le :
    4 ≤ Fintype.card (V13F2LinearEquiv 2) := by
  classical
  have hsub :
      Fintype.card (V13RealLinearUniformTargetRowOccurrence (0 : Fin 2)) ≤
        Fintype.card (V13F2LinearEquiv 2) := by
    change
      Fintype.card
          {A : V13F2LinearEquiv 2 //
            (V13RealLinearTargetRows A (0 : Fin 2)).Nonempty} ≤
        Fintype.card (V13F2LinearEquiv 2)
    exact
      Fintype.card_subtype_le
        (fun A : V13F2LinearEquiv 2 =>
          (V13RealLinearTargetRows A (0 : Fin 2)).Nonempty)
  exact v13RealLinearUniformTargetRowOccurrence_card_four_le.trans hsub

theorem v13RealLinearUniformTargetRowOccurrenceMass_two_zero_gt_half_unconditional :
    (1 / 2 : Rat) <
      v13RealLinearUniformTargetRowOccurrenceMass (0 : Fin 2) :=
  v13RealLinearUniformTargetRowOccurrenceMass_two_zero_gt_half
    v13RealLinear_f2_equiv_two_card_le_six

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

/-- Coefficient-certified generated worlds.  This expands the generated event
by carrying an explicit row-combination witness for the realized branch. -/
def V13RealLinearAdaptiveQRowGeneratedCoefficient {m q : Nat}
    {Seed : Type*} (E : V13RealLinearAdaptiveQRowExperiment m q Seed)
    (i₀ : Fin m) :=
  {data :
      (Σ omega : V13RealLinearAdaptiveQRowWorld m Seed,
        V13RealLinearRowCombination (E.branchRows omega)) //
    ∀ w : F2Vec m,
      v13RealLinearRowCombinationEval
          (E.sampleA data.1.1) (E.branchRows data.1)
          data.2 w = w i₀}

/-- The fixed-seed fiber of coefficient-certified generated worlds.  For the
uniform sampler, the seed is the sampled certified invertible map `A`. -/
def V13RealLinearAdaptiveQRowGeneratedCoefficientFiber {m q : Nat}
    {Seed : Type*} (E : V13RealLinearAdaptiveQRowExperiment m q Seed)
    (i₀ : Fin m) (seed : Seed) :=
  {data :
      (Σ x : F2Vec m,
        V13RealLinearRowCombination (E.branchRows (seed, x))) //
    ∀ w : F2Vec m,
      v13RealLinearRowCombinationEval
          (E.sampleA seed) (E.branchRows (seed, data.1))
          data.2 w = w i₀}

/-- Fixed-seed coefficient fibers with the target equation factored into the
rowset certificate itself.  For each hidden vector `x`, the certificate says
that the rowset chosen by the realized causal branch spans the target
coordinate. -/
def V13RealLinearAdaptiveQRowGeneratedTargetCoefficientFiber {m q : Nat}
    {Seed : Type*} (E : V13RealLinearAdaptiveQRowExperiment m q Seed)
    (i₀ : Fin m) (seed : Seed) :=
  Σ x : F2Vec m,
    V13RealLinearRowsTargetCoefficient
      (E.sampleA seed) (E.branchRows (seed, x)) i₀

/-- A fixed-map target-coefficient fiber cell after exposing the realized
finite rowset.  The equality records that the hidden vector lands in this
rowset cell for the causal branch actually selected by the public instance. -/
def V13RealLinearAdaptiveQRowGeneratedTargetCoefficientRowsetCell {m q : Nat}
    {Seed : Type*} (E : V13RealLinearAdaptiveQRowExperiment m q Seed)
    (i₀ : Fin m) (seed : Seed) (rows : Finset (Fin m)) :=
  {cert :
      V13RealLinearAdaptiveQRowGeneratedTargetCoefficientFiber E i₀ seed //
    E.branchRows (seed, cert.1) = rows}

/-- Hidden vectors whose realized causal branch has exactly the given rowset. -/
def V13RealLinearAdaptiveQRowRowsetFiber {m q : Nat}
    {Seed : Type*} (E : V13RealLinearAdaptiveQRowExperiment m q Seed)
    (seed : Seed) (rows : Finset (Fin m)) :=
  {x : F2Vec m // E.branchRows (seed, x) = rows}

/-- Rowsets within the q-row read budget. -/
abbrev V13RealLinearBudgetedRowset (m q : Nat) :=
  {rows : Finset (Fin m) // rows.card ≤ q}

/-- Product form of a fixed-map rowset cell: choose the hidden vector landing in
the rowset cell, then choose the rowset-local target coefficient. -/
abbrev V13RealLinearAdaptiveQRowGeneratedTargetCoefficientRowsetProductCell
    {m q : Nat} {Seed : Type*}
    (E : V13RealLinearAdaptiveQRowExperiment m q Seed)
    (i₀ : Fin m) (seed : Seed) (rows : Finset (Fin m)) :=
  V13RealLinearAdaptiveQRowRowsetFiber E seed rows ×
    V13RealLinearRowsTargetCoefficient (E.sampleA seed) rows i₀

noncomputable instance {m q : Nat} {Seed : Type*} [Fintype Seed]
    (E : V13RealLinearAdaptiveQRowExperiment m q Seed) (i₀ : Fin m) :
    Fintype (V13RealLinearAdaptiveQRowGeneratedCoefficient E i₀) := by
  classical
  unfold V13RealLinearAdaptiveQRowGeneratedCoefficient
  infer_instance

noncomputable instance {m q : Nat} {Seed : Type*} [Fintype Seed]
    (E : V13RealLinearAdaptiveQRowExperiment m q Seed) (i₀ : Fin m)
    (seed : Seed) :
    Fintype (V13RealLinearAdaptiveQRowGeneratedCoefficientFiber E i₀ seed) := by
  classical
  unfold V13RealLinearAdaptiveQRowGeneratedCoefficientFiber
  infer_instance

noncomputable instance {m q : Nat} {Seed : Type*} [Fintype Seed]
    (E : V13RealLinearAdaptiveQRowExperiment m q Seed) (i₀ : Fin m)
    (seed : Seed) :
    Fintype
      (V13RealLinearAdaptiveQRowGeneratedTargetCoefficientFiber E i₀ seed) := by
  classical
  unfold V13RealLinearAdaptiveQRowGeneratedTargetCoefficientFiber
  infer_instance

noncomputable instance {m q : Nat} {Seed : Type*} [Fintype Seed]
    (E : V13RealLinearAdaptiveQRowExperiment m q Seed) (i₀ : Fin m)
    (seed : Seed) (rows : Finset (Fin m)) :
    Fintype
      (V13RealLinearAdaptiveQRowGeneratedTargetCoefficientRowsetCell
        E i₀ seed rows) := by
  classical
  unfold V13RealLinearAdaptiveQRowGeneratedTargetCoefficientRowsetCell
  infer_instance

noncomputable instance {m q : Nat} {Seed : Type*} [Fintype Seed]
    (E : V13RealLinearAdaptiveQRowExperiment m q Seed)
    (seed : Seed) (rows : Finset (Fin m)) :
    Fintype (V13RealLinearAdaptiveQRowRowsetFiber E seed rows) := by
  classical
  unfold V13RealLinearAdaptiveQRowRowsetFiber
  infer_instance

theorem v13RealLinearAdaptiveQRowRowsetFiber_card_eq_zero_of_q_lt_rows_card
    {m q : Nat} {Seed : Type*} [Fintype Seed]
    (E : V13RealLinearAdaptiveQRowExperiment m q Seed)
    (seed : Seed) (rows : Finset (Fin m)) (hrows : q < rows.card) :
    Fintype.card (V13RealLinearAdaptiveQRowRowsetFiber E seed rows) = 0 := by
  classical
  rw [Fintype.card_eq_zero_iff]
  exact
    ⟨fun x =>
      have hle : rows.card ≤ q := by
        simpa [x.property] using E.branchRows_card_le (seed, x.val)
      (Nat.not_le_of_gt hrows) hle⟩

noncomputable def
    v13RealLinearAdaptiveQRowGeneratedTargetCoefficientRowsetCellEquivProduct
    {m q : Nat} {Seed : Type*}
    (E : V13RealLinearAdaptiveQRowExperiment m q Seed) (i₀ : Fin m)
    (seed : Seed) (rows : Finset (Fin m)) :
    V13RealLinearAdaptiveQRowGeneratedTargetCoefficientRowsetCell
        E i₀ seed rows ≃
      V13RealLinearAdaptiveQRowGeneratedTargetCoefficientRowsetProductCell
        E i₀ seed rows where
  toFun cell := by
    let cert := cell.val
    let hrows : E.branchRows (seed, cert.1) = rows := cell.property
    exact ⟨⟨cert.1, hrows⟩, hrows ▸ cert.2⟩
  invFun cell := by
    let x := cell.1
    let coeff := cell.2
    exact ⟨⟨x.val, x.property.symm ▸ coeff⟩, x.property⟩
  left_inv cell := by
    rcases cell with ⟨⟨x, coeff⟩, hrows⟩
    cases hrows
    rfl
  right_inv cell := by
    rcases cell with ⟨⟨x, hrows⟩, coeff⟩
    cases hrows
    rfl

theorem v13RealLinearAdaptiveQRowGeneratedTargetCoefficientRowsetCell_card_eq_product
    {m q : Nat} {Seed : Type*} [Fintype Seed]
    (E : V13RealLinearAdaptiveQRowExperiment m q Seed) (i₀ : Fin m)
    (seed : Seed) (rows : Finset (Fin m)) :
    Fintype.card
        (V13RealLinearAdaptiveQRowGeneratedTargetCoefficientRowsetCell
          E i₀ seed rows) =
      Fintype.card (V13RealLinearAdaptiveQRowRowsetFiber E seed rows) *
        Fintype.card
          (V13RealLinearRowsTargetCoefficient (E.sampleA seed) rows i₀) := by
  classical
  rw [Fintype.card_congr
    (v13RealLinearAdaptiveQRowGeneratedTargetCoefficientRowsetCellEquivProduct
      E i₀ seed rows)]
  rw [Fintype.card_prod]

theorem v13RealLinearAdaptiveQRow_rowsetProduct_sum_eq_budgeted
    {m q : Nat} {Seed : Type*} [Fintype Seed]
    (E : V13RealLinearAdaptiveQRowExperiment m q Seed) (i₀ : Fin m)
    (seed : Seed) :
    (∑ rows : Finset (Fin m),
        Fintype.card (V13RealLinearAdaptiveQRowRowsetFiber E seed rows) *
          Fintype.card
            (V13RealLinearRowsTargetCoefficient (E.sampleA seed) rows i₀)) =
      ∑ rows : V13RealLinearBudgetedRowset m q,
        Fintype.card
            (V13RealLinearAdaptiveQRowRowsetFiber E seed rows.val) *
          Fintype.card
            (V13RealLinearRowsTargetCoefficient
              (E.sampleA seed) rows.val i₀) := by
  classical
  let f : Finset (Fin m) → Nat := fun rows =>
    Fintype.card (V13RealLinearAdaptiveQRowRowsetFiber E seed rows) *
      Fintype.card
        (V13RealLinearRowsTargetCoefficient (E.sampleA seed) rows i₀)
  have hsplit :
      (∑ rows : Finset (Fin m), f rows) =
        (∑ rows : V13RealLinearBudgetedRowset m q, f rows.val) +
          ∑ rows : {rows : Finset (Fin m) // ¬ rows.card ≤ q},
            f rows.val := by
    simpa [f, V13RealLinearBudgetedRowset] using
      (Fintype.sum_subtype_add_sum_subtype
        (fun rows : Finset (Fin m) => rows.card ≤ q) f).symm
  have hbad :
      (∑ rows : {rows : Finset (Fin m) // ¬ rows.card ≤ q},
          f rows.val) = 0 := by
    apply Finset.sum_eq_zero
    intro rows _
    have hgt : q < rows.val.card := Nat.lt_of_not_ge rows.property
    have hfiber :=
      v13RealLinearAdaptiveQRowRowsetFiber_card_eq_zero_of_q_lt_rows_card
        E seed rows.val hgt
    simp [f, hfiber]
  calc
    (∑ rows : Finset (Fin m),
        Fintype.card (V13RealLinearAdaptiveQRowRowsetFiber E seed rows) *
          Fintype.card
            (V13RealLinearRowsTargetCoefficient (E.sampleA seed) rows i₀)) =
        ∑ rows : Finset (Fin m), f rows := rfl
    _ =
        (∑ rows : V13RealLinearBudgetedRowset m q, f rows.val) +
          ∑ rows : {rows : Finset (Fin m) // ¬ rows.card ≤ q},
            f rows.val := hsplit
    _ = ∑ rows : V13RealLinearBudgetedRowset m q, f rows.val := by
      rw [hbad, Nat.add_zero]
    _ =
        ∑ rows : V13RealLinearBudgetedRowset m q,
          Fintype.card
              (V13RealLinearAdaptiveQRowRowsetFiber E seed rows.val) *
            Fintype.card
              (V13RealLinearRowsTargetCoefficient
                (E.sampleA seed) rows.val i₀) := rfl

noncomputable def
    v13RealLinearAdaptiveQRowGeneratedTargetCoefficientFiberEquivSigmaRowsetCell
    {m q : Nat} {Seed : Type*}
    (E : V13RealLinearAdaptiveQRowExperiment m q Seed) (i₀ : Fin m)
    (seed : Seed) :
    V13RealLinearAdaptiveQRowGeneratedTargetCoefficientFiber E i₀ seed ≃
      (Σ rows : Finset (Fin m),
        V13RealLinearAdaptiveQRowGeneratedTargetCoefficientRowsetCell
          E i₀ seed rows) where
  toFun cert :=
    ⟨E.branchRows (seed, cert.1), ⟨cert, rfl⟩⟩
  invFun cell := by
    rcases cell with ⟨rows, cell⟩
    rcases cell with ⟨cert, hrows⟩
    cases hrows
    exact cert
  left_inv cert := by
    rfl
  right_inv cell := by
    rcases cell with ⟨rows, cell⟩
    rcases cell with ⟨cert, hrows⟩
    cases hrows
    rfl

theorem v13RealLinearAdaptiveQRowGeneratedTargetCoefficientFiber_card_eq_sum_rowsetCells
    {m q : Nat} {Seed : Type*} [Fintype Seed]
    (E : V13RealLinearAdaptiveQRowExperiment m q Seed) (i₀ : Fin m)
    (seed : Seed) :
    Fintype.card
        (V13RealLinearAdaptiveQRowGeneratedTargetCoefficientFiber E i₀ seed) =
      ∑ rows : Finset (Fin m),
        Fintype.card
          (V13RealLinearAdaptiveQRowGeneratedTargetCoefficientRowsetCell
            E i₀ seed rows) := by
  classical
  rw [Fintype.card_congr
    (v13RealLinearAdaptiveQRowGeneratedTargetCoefficientFiberEquivSigmaRowsetCell
      E i₀ seed)]
  rw [Fintype.card_sigma]

noncomputable def
    v13RealLinearAdaptiveQRowGeneratedCoefficientFiberEquivTargetCoefficientFiber
    {m q : Nat} {Seed : Type*}
    (E : V13RealLinearAdaptiveQRowExperiment m q Seed) (i₀ : Fin m)
    (seed : Seed) :
    V13RealLinearAdaptiveQRowGeneratedCoefficientFiber E i₀ seed ≃
      V13RealLinearAdaptiveQRowGeneratedTargetCoefficientFiber E i₀ seed where
  toFun cert := ⟨cert.val.1, ⟨cert.val.2, cert.property⟩⟩
  invFun cert := ⟨⟨cert.1, cert.2.val⟩, cert.2.property⟩
  left_inv cert := by
    rfl
  right_inv cert := by
    rfl

theorem v13RealLinearAdaptiveQRowGeneratedCoefficientFiber_card_eq_targetCoefficientFiber
    {m q : Nat} {Seed : Type*} [Fintype Seed]
    (E : V13RealLinearAdaptiveQRowExperiment m q Seed) (i₀ : Fin m)
    (seed : Seed) :
    Fintype.card (V13RealLinearAdaptiveQRowGeneratedCoefficientFiber E i₀ seed) =
      Fintype.card
        (V13RealLinearAdaptiveQRowGeneratedTargetCoefficientFiber E i₀ seed) := by
  classical
  exact Fintype.card_congr
    (v13RealLinearAdaptiveQRowGeneratedCoefficientFiberEquivTargetCoefficientFiber
      E i₀ seed)

noncomputable def v13RealLinearAdaptiveQRowGeneratedCoefficientEquivSigmaFiber
    {m q : Nat} {Seed : Type*}
    (E : V13RealLinearAdaptiveQRowExperiment m q Seed) (i₀ : Fin m) :
    V13RealLinearAdaptiveQRowGeneratedCoefficient E i₀ ≃
      (Σ seed : Seed,
        V13RealLinearAdaptiveQRowGeneratedCoefficientFiber E i₀ seed) where
  toFun cert :=
    ⟨cert.val.1.1,
      ⟨⟨cert.val.1.2, cert.val.2⟩, cert.property⟩⟩
  invFun cert :=
    ⟨⟨(cert.1, cert.2.val.1), cert.2.val.2⟩, cert.2.property⟩
  left_inv cert := by
    rfl
  right_inv cert := by
    rfl

theorem v13RealLinearAdaptiveQRowGeneratedCoefficient_card_eq_sum_fibers
    {m q : Nat} {Seed : Type*} [Fintype Seed]
    (E : V13RealLinearAdaptiveQRowExperiment m q Seed) (i₀ : Fin m) :
    Fintype.card (V13RealLinearAdaptiveQRowGeneratedCoefficient E i₀) =
      ∑ seed : Seed,
        Fintype.card
          (V13RealLinearAdaptiveQRowGeneratedCoefficientFiber E i₀ seed) := by
  classical
  rw [Fintype.card_congr
    (v13RealLinearAdaptiveQRowGeneratedCoefficientEquivSigmaFiber E i₀)]
  rw [Fintype.card_sigma]

noncomputable def v13RealLinearAdaptiveQRowGeneratedToCoefficient
    {m q : Nat} {Seed : Type*}
    (E : V13RealLinearAdaptiveQRowExperiment m q Seed) (i₀ : Fin m) :
    V13RealLinearAdaptiveQRowGenerated E i₀ ↪
      V13RealLinearAdaptiveQRowGeneratedCoefficient E i₀ where
  toFun omega := by
    classical
    exact
      ⟨⟨omega.val, Classical.choose omega.property⟩,
        Classical.choose_spec omega.property⟩
  inj' := by
    intro omega₀ omega₁ hmap
    apply Subtype.ext
    exact
      congrArg
        (fun cert : V13RealLinearAdaptiveQRowGeneratedCoefficient E i₀ =>
          cert.val.1)
        hmap

theorem v13RealLinearAdaptiveQRowGenerated_card_le_coefficient
    {m q : Nat} {Seed : Type*} [Fintype Seed]
    (E : V13RealLinearAdaptiveQRowExperiment m q Seed) (i₀ : Fin m) :
    Fintype.card (V13RealLinearAdaptiveQRowGenerated E i₀) ≤
      Fintype.card (V13RealLinearAdaptiveQRowGeneratedCoefficient E i₀) :=
  Fintype.card_le_of_embedding
    (v13RealLinearAdaptiveQRowGeneratedToCoefficient E i₀)

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

/-- The refined single remaining pin: under the causal row-query interface,
the realized branch generates the target functional with mass at most
`2^q / 2^m`.  The earlier full-map branch interface is intentionally not used
for the final q-row theorem. -/
def V13RealLinearUniformCausalRowSpanCountingBound {m q : Nat}
    (observer : V13RealLinearCausalRowObserver m q) (i₀ : Fin m) : Prop :=
  V13RealLinearAdaptiveRowSpanCountingBound
    (v13RealLinearUniformCausalQRowExperiment observer) i₀

theorem v13RealLinearUniformCausalRowSpanCountingBound_of_generated_counting
    {m q : Nat} (observer : V13RealLinearCausalRowObserver m q)
    (i₀ : Fin m)
    (hcount :
      Fintype.card
          (V13RealLinearAdaptiveQRowGenerated
            (v13RealLinearUniformCausalQRowExperiment observer) i₀) *
        2 ^ m ≤
      2 ^ q *
        Fintype.card
          (V13RealLinearAdaptiveQRowWorld m (V13F2LinearEquiv m))) :
    V13RealLinearUniformCausalRowSpanCountingBound observer i₀ := by
  unfold V13RealLinearUniformCausalRowSpanCountingBound
  unfold V13RealLinearAdaptiveRowSpanCountingBound
  unfold v13RealLinearAdaptiveQRowGeneratedMass
  unfold v13RealLinearQRowEpsilon
  let G := Fintype.card
    (V13RealLinearAdaptiveQRowGenerated
      (v13RealLinearUniformCausalQRowExperiment observer) i₀)
  let T := Fintype.card
    (V13RealLinearAdaptiveQRowWorld m (V13F2LinearEquiv m))
  let Q := 2 ^ q
  let M := 2 ^ m
  have hcard : G * M ≤ Q * T := by
    simpa [G, T, Q, M] using hcount
  have hTposNat : 0 < T := by
    dsimp [T]
    exact Fintype.card_pos_iff.mpr ⟨(v13RealLinearIdentity m, f2ZeroVec m)⟩
  have hMposNat : 0 < M := by
    dsimp [M]
    positivity
  have hTpos : (0 : Rat) < (T : Rat) := by
    exact_mod_cast hTposNat
  have hMpos : (0 : Rat) < (M : Rat) := by
    exact_mod_cast hMposNat
  have hcardRat : (G : Rat) * (M : Rat) ≤ (Q : Rat) * (T : Rat) := by
    exact_mod_cast hcard
  have hQrat : (2 : Rat) ^ q = (Q : Rat) := by
    dsimp [Q]
    norm_num
  have hMrat : (2 : Rat) ^ m = (M : Rat) := by
    dsimp [M]
    norm_num
  rw [hQrat, hMrat]
  change (G : Rat) / (T : Rat) ≤ (Q : Rat) / (M : Rat)
  rw [div_le_div_iff₀ hTpos hMpos]
  exact hcardRat

theorem v13RealLinearUniformCausalRowSpanCountingBound_of_zero_budget
    {m : Nat} (observer : V13RealLinearCausalRowObserver m 0)
    (i₀ : Fin m) :
    V13RealLinearUniformCausalRowSpanCountingBound observer i₀ :=
  v13RealLinearAdaptiveRowSpanCountingBound_of_zero_budget
    (v13RealLinearUniformCausalQRowExperiment observer) i₀

theorem v13RealLinearUniformCausalRowSpanCountingBound_of_m_le_q
    {m q : Nat} (observer : V13RealLinearCausalRowObserver m q)
    (i₀ : Fin m) (hmq : m ≤ q) :
    V13RealLinearUniformCausalRowSpanCountingBound observer i₀ :=
  v13RealLinearAdaptiveRowSpanCountingBound_of_m_le_q
    (v13RealLinearUniformCausalQRowExperiment observer) i₀ hmq

theorem v13RealLinear_targetRowObserver_spanCountingBound_fails_two_zero
    (hcard : Fintype.card (V13F2LinearEquiv 2) ≤ 6) :
    ¬ V13RealLinearUniformInvertibleRowSpanCountingBound
        (v13RealLinearTargetRowObserver (0 : Fin 2)) (0 : Fin 2) := by
  intro hbound
  unfold V13RealLinearUniformInvertibleRowSpanCountingBound at hbound
  unfold V13RealLinearAdaptiveRowSpanCountingBound at hbound
  rw [v13RealLinear_targetRowObserverGeneratedMass_eq_occurrenceMass] at hbound
  unfold v13RealLinearQRowEpsilon at hbound
  norm_num at hbound
  exact
    not_lt_of_ge hbound
      (v13RealLinearUniformTargetRowOccurrenceMass_two_zero_gt_half hcard)

theorem v13RealLinear_targetRowObserver_spanCountingBound_fails_two_zero_unconditional :
    ¬ V13RealLinearUniformInvertibleRowSpanCountingBound
        (v13RealLinearTargetRowObserver (0 : Fin 2)) (0 : Fin 2) :=
  v13RealLinear_targetRowObserver_spanCountingBound_fails_two_zero
    v13RealLinear_f2_equiv_two_card_le_six

noncomputable def v13RealLinearUniformAdaptiveQRowSuccess {m q : Nat}
    (observer : V13RealLinearAdaptiveRowObserver m q) (i₀ : Fin m) : Rat :=
  v13RealLinearAdaptiveQRowSuccess
    (v13RealLinearUniformQRowExperiment observer) i₀

noncomputable def v13RealLinearUniformCausalQRowSuccess {m q : Nat}
    (observer : V13RealLinearCausalRowObserver m q) (i₀ : Fin m) : Rat :=
  v13RealLinearAdaptiveQRowSuccess
    (v13RealLinearUniformCausalQRowExperiment observer) i₀

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

theorem v13RealLinear_uniform_causal_qrow_success_bound_of_spanCounting
    {m q : Nat} (observer : V13RealLinearCausalRowObserver m q)
    (i₀ : Fin m)
    (hcount :
      V13RealLinearUniformCausalRowSpanCountingBound observer i₀) :
    v13RealLinearUniformCausalQRowSuccess observer i₀ ≤
      (1 / 2 : Rat) + v13RealLinearQRowEpsilon q m := by
  exact
    v13RealLinear_adaptive_qrow_success_bound_of_spanCounting
      (v13RealLinearUniformCausalQRowExperiment observer) i₀ hcount

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

theorem v13RealLinear_uniform_causal_zero_row_success_bound
    {m : Nat} (observer : V13RealLinearCausalRowObserver m 0)
    (i₀ : Fin m) :
    v13RealLinearUniformCausalQRowSuccess observer i₀ ≤
      (1 / 2 : Rat) + v13RealLinearQRowEpsilon 0 m := by
  exact
    v13RealLinear_uniform_causal_qrow_success_bound_of_spanCounting
      observer i₀
      (v13RealLinearUniformCausalRowSpanCountingBound_of_zero_budget
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

theorem v13RealLinear_uniform_causal_high_budget_success_bound
    {m q : Nat} (observer : V13RealLinearCausalRowObserver m q)
    (i₀ : Fin m) (hmq : m ≤ q) :
    v13RealLinearUniformCausalQRowSuccess observer i₀ ≤
      (1 / 2 : Rat) + v13RealLinearQRowEpsilon q m := by
  exact
    v13RealLinear_uniform_causal_qrow_success_bound_of_spanCounting
      observer i₀
      (v13RealLinearUniformCausalRowSpanCountingBound_of_m_le_q
        observer i₀ hmq)

/-- The sole low-positive counting input left for the causal row-query route.
Zero-row and high-budget cases are already closed, so this statement is only
asked for `0 < q` and `q < m`. -/
def V13RealLinearUniformCausalLowPositiveRowSpanCountingBound : Prop :=
  ∀ {m q : Nat} (observer : V13RealLinearCausalRowObserver m q)
    (i₀ : Fin m),
    0 < q → q < m →
      V13RealLinearUniformCausalRowSpanCountingBound observer i₀

/-- Cardinal form of the low-positive causal counting problem.  It asks for
the generated/span-hit worlds to occupy at most a `2^q / 2^m` fraction of all
uniform certified-invertible worlds, stated without division. -/
def V13RealLinearUniformCausalLowPositiveCompletionCountingBound : Prop :=
  ∀ {m q : Nat} (observer : V13RealLinearCausalRowObserver m q)
    (i₀ : Fin m),
    0 < q → q < m →
      Fintype.card
          (V13RealLinearAdaptiveQRowGenerated
            (v13RealLinearUniformCausalQRowExperiment observer) i₀) *
        2 ^ m ≤
      2 ^ q *
        Fintype.card
          (V13RealLinearAdaptiveQRowWorld m (V13F2LinearEquiv m))

/-- Coefficient-certificate form of the low-positive causal counting problem.
It bounds generated worlds after expanding each one by an explicit
row-combination witness for the realized branch. -/
def V13RealLinearUniformCausalLowPositiveCoefficientCountingBound : Prop :=
  ∀ {m q : Nat} (observer : V13RealLinearCausalRowObserver m q)
    (i₀ : Fin m),
    0 < q → q < m →
      Fintype.card
          (V13RealLinearAdaptiveQRowGeneratedCoefficient
            (v13RealLinearUniformCausalQRowExperiment observer) i₀) *
        2 ^ m ≤
      2 ^ q *
        Fintype.card
          (V13RealLinearAdaptiveQRowWorld m (V13F2LinearEquiv m))

/-- Fixed-map fiber form of the low-positive causal counting problem.  It asks
that after the sampled invertible map `A` is fixed, at most `2^q` hidden
witness/coefficient pairs can certify that the realized causal branch generated
the target. -/
def V13RealLinearUniformCausalLowPositiveFiberCoefficientCountingBound : Prop :=
  ∀ {m q : Nat} (observer : V13RealLinearCausalRowObserver m q)
    (i₀ : Fin m),
    0 < q → q < m →
      ∀ A : V13F2LinearEquiv m,
        Fintype.card
            (V13RealLinearAdaptiveQRowGeneratedCoefficientFiber
              (v13RealLinearUniformCausalQRowExperiment observer) i₀ A) ≤
          2 ^ q

/-- Residual row-span form after the zero-budget, high-budget, and q = 1
cases have been closed. -/
def V13RealLinearUniformCausalTwoOrMoreRowSpanCountingBound : Prop :=
  ∀ {m q : Nat} (observer : V13RealLinearCausalRowObserver m q)
    (i₀ : Fin m),
    1 < q → q < m →
      V13RealLinearUniformCausalRowSpanCountingBound observer i₀

/-- Residual cardinal form after the zero-budget, high-budget, and q = 1 cases
have been closed. -/
def V13RealLinearUniformCausalTwoOrMoreCompletionCountingBound : Prop :=
  ∀ {m q : Nat} (observer : V13RealLinearCausalRowObserver m q)
    (i₀ : Fin m),
    1 < q → q < m →
      Fintype.card
          (V13RealLinearAdaptiveQRowGenerated
            (v13RealLinearUniformCausalQRowExperiment observer) i₀) *
        2 ^ m ≤
      2 ^ q *
        Fintype.card
          (V13RealLinearAdaptiveQRowWorld m (V13F2LinearEquiv m))

/-- Residual coefficient-certificate form after the zero-budget, high-budget,
and q = 1 cases have been closed. -/
def V13RealLinearUniformCausalTwoOrMoreCoefficientCountingBound : Prop :=
  ∀ {m q : Nat} (observer : V13RealLinearCausalRowObserver m q)
    (i₀ : Fin m),
    1 < q → q < m →
      Fintype.card
          (V13RealLinearAdaptiveQRowGeneratedCoefficient
            (v13RealLinearUniformCausalQRowExperiment observer) i₀) *
        2 ^ m ≤
      2 ^ q *
        Fintype.card
          (V13RealLinearAdaptiveQRowWorld m (V13F2LinearEquiv m))

/-- Compressed residual coefficient form.  Since the uniform world count is
`card GL(m,2) * 2^m`, this is the coefficient-counting hard core with the
hidden-vector factor cancelled. -/
def V13RealLinearUniformCausalTwoOrMoreCoefficientCompressionBound : Prop :=
  ∀ {m q : Nat} (observer : V13RealLinearCausalRowObserver m q)
    (i₀ : Fin m),
    1 < q → q < m →
      Fintype.card
          (V13RealLinearAdaptiveQRowGeneratedCoefficient
            (v13RealLinearUniformCausalQRowExperiment observer) i₀) ≤
      2 ^ q * Fintype.card (V13F2LinearEquiv m)

/-- Average-fiber residual coefficient form.  The pointwise fixed-map fiber
bound is too strong, but the compressed hard core is exactly the statement that
the fixed-map coefficient fibers have average size at most `2^q`. -/
def V13RealLinearUniformCausalTwoOrMoreFiberAverageCoefficientBound : Prop :=
  ∀ {m q : Nat} (observer : V13RealLinearCausalRowObserver m q)
    (i₀ : Fin m),
    1 < q → q < m →
      (∑ A : V13F2LinearEquiv m,
        Fintype.card
          (V13RealLinearAdaptiveQRowGeneratedCoefficientFiber
            (v13RealLinearUniformCausalQRowExperiment observer) i₀ A)) ≤
      2 ^ q * Fintype.card (V13F2LinearEquiv m)

/-- Target-coefficient version of the average-fiber residual form.  This is
definitionally the same fixed-map fiber problem, but the coefficient equation is
factored into a rowset-local certificate. -/
def V13RealLinearUniformCausalTwoOrMoreTargetCoefficientFiberAverageBound :
    Prop :=
  ∀ {m q : Nat} (observer : V13RealLinearCausalRowObserver m q)
    (i₀ : Fin m),
    1 < q → q < m →
      (∑ A : V13F2LinearEquiv m,
        Fintype.card
          (V13RealLinearAdaptiveQRowGeneratedTargetCoefficientFiber
            (v13RealLinearUniformCausalQRowExperiment observer) i₀ A)) ≤
      2 ^ q * Fintype.card (V13F2LinearEquiv m)

/-- Rowset-cell version of the target-coefficient average hard core.  It
keeps the branch type abstract and finite-splits only by the realized rowset,
which is a finite value even when the causal branch type is not finite. -/
def V13RealLinearUniformCausalTwoOrMoreTargetCoefficientRowsetAverageBound :
    Prop :=
  ∀ {m q : Nat} (observer : V13RealLinearCausalRowObserver m q)
    (i₀ : Fin m),
    1 < q → q < m →
      (∑ A : V13F2LinearEquiv m,
        ∑ rows : Finset (Fin m),
          Fintype.card
            (V13RealLinearAdaptiveQRowGeneratedTargetCoefficientRowsetCell
              (v13RealLinearUniformCausalQRowExperiment observer) i₀ A rows)) ≤
      2 ^ q * Fintype.card (V13F2LinearEquiv m)

/-- Product-count version of the rowset-cell hard core.  For each fixed map
and realized rowset, the cell count is the number of hidden vectors landing in
that rowset times the number of rowset-local target coefficients. -/
def V13RealLinearUniformCausalTwoOrMoreTargetCoefficientRowsetProductAverageBound :
    Prop :=
  ∀ {m q : Nat} (observer : V13RealLinearCausalRowObserver m q)
    (i₀ : Fin m),
    1 < q → q < m →
      (∑ A : V13F2LinearEquiv m,
        ∑ rows : Finset (Fin m),
          Fintype.card
              (V13RealLinearAdaptiveQRowRowsetFiber
                (v13RealLinearUniformCausalQRowExperiment observer) A rows) *
            Fintype.card
              (V13RealLinearRowsTargetCoefficient A rows i₀)) ≤
      2 ^ q * Fintype.card (V13F2LinearEquiv m)

/-- Budgeted-rowset product form of the residual hard core.  This is the same
product count with the impossible over-budget rowsets removed from the finite
index type. -/
def
    V13RealLinearUniformCausalTwoOrMoreTargetCoefficientBudgetedRowsetProductAverageBound :
    Prop :=
  ∀ {m q : Nat} (observer : V13RealLinearCausalRowObserver m q)
    (i₀ : Fin m),
    1 < q → q < m →
      (∑ A : V13F2LinearEquiv m,
        ∑ rows : V13RealLinearBudgetedRowset m q,
          Fintype.card
              (V13RealLinearAdaptiveQRowRowsetFiber
                (v13RealLinearUniformCausalQRowExperiment observer) A
                rows.val) *
            Fintype.card
              (V13RealLinearRowsTargetCoefficient A rows.val i₀)) ≤
      2 ^ q * Fintype.card (V13F2LinearEquiv m)

theorem v13RealLinear_f2vec_card (m : Nat) :
    Fintype.card (F2Vec m) = 2 ^ m := by
  classical
  simp [F2Vec]

theorem v13RealLinearRowIndexedFixedTargetRowOccurrenceWorld_card_eq_sum
    {m : Nat} (i₀ : Fin m) :
    Fintype.card
        (V13RealLinearRowIndexedFixedTargetRowOccurrenceWorld m i₀) =
      ∑ row : Fin m,
        Fintype.card
          (V13RealLinearUniformFixedTargetRowOccurrence row i₀ × F2Vec m) := by
  classical
  rw [Fintype.card_congr
    (v13RealLinearRowIndexedFixedTargetRowOccurrenceWorldEquiv i₀)]
  rw [Fintype.card_sigma]

theorem v13RealLinearRowIndexedFixedTargetRowOccurrenceWorld_card_le
    {m : Nat} (i₀ : Fin m) :
    Fintype.card
        (V13RealLinearRowIndexedFixedTargetRowOccurrenceWorld m i₀) ≤
      Fintype.card (Fin m) *
        (2 * Fintype.card (V13F2LinearEquiv m)) := by
  classical
  rw [v13RealLinearRowIndexedFixedTargetRowOccurrenceWorld_card_eq_sum i₀]
  have hsum :
      (∑ row : Fin m,
        Fintype.card
          (V13RealLinearUniformFixedTargetRowOccurrence row i₀ × F2Vec m)) ≤
        ∑ _row : Fin m,
          2 * Fintype.card (V13F2LinearEquiv m) := by
    apply Finset.sum_le_sum
    intro row _hrow
    rw [Fintype.card_prod, v13RealLinear_f2vec_card]
    exact v13RealLinearFixedTargetRowOccurrence_counting row i₀
  simpa using hsum

noncomputable def v13RealLinearUniformOneRowGeneratedToRowIndexedFixedOccurrence
    {m : Nat} (observer : V13RealLinearAdaptiveRowObserver m 1)
    (i₀ : Fin m) :
    V13RealLinearAdaptiveQRowGenerated
        (v13RealLinearUniformQRowExperiment observer) i₀ ↪
      V13RealLinearRowIndexedFixedTargetRowOccurrenceWorld m i₀ where
  toFun omega := by
    classical
    let htargetExists :=
        V13RealLinearAdaptiveQRowExperiment.generated_one_budget_exists_target_row
          (v13RealLinearUniformQRowExperiment observer) i₀ omega.val
          omega.property
    let row : Fin m := Classical.choose htargetExists
    have htarget :
        ∀ w : F2Vec m, omega.val.1.toEquiv w row = w i₀ := by
      have hspec := Classical.choose_spec htargetExists
      simpa [v13RealLinearUniformQRowExperiment, row] using hspec.2
    exact
      { row := row
        A := omega.val.1
        x := omega.val.2
        targetRow :=
          (v13RealLinear_mem_targetRows_iff omega.val.1 i₀ row).2
            htarget }
  inj' := by
    intro omega₀ omega₁ hmap
    apply Subtype.ext
    apply Prod.ext
    · exact
        congrArg
          V13RealLinearRowIndexedFixedTargetRowOccurrenceWorld.A hmap
    · exact
        congrArg
          V13RealLinearRowIndexedFixedTargetRowOccurrenceWorld.x hmap

theorem v13RealLinearUniformOneRowGenerated_card_le_rowIndexedFixedOccurrence
    {m : Nat} (observer : V13RealLinearAdaptiveRowObserver m 1)
    (i₀ : Fin m) :
    Fintype.card
        (V13RealLinearAdaptiveQRowGenerated
          (v13RealLinearUniformQRowExperiment observer) i₀) ≤
      Fintype.card
        (V13RealLinearRowIndexedFixedTargetRowOccurrenceWorld m i₀) :=
  Fintype.card_le_of_embedding
    (v13RealLinearUniformOneRowGeneratedToRowIndexedFixedOccurrence
      observer i₀)

theorem v13RealLinearUniformOneRowGenerated_counting_with_rowFactor
    {m : Nat} (observer : V13RealLinearAdaptiveRowObserver m 1)
    (i₀ : Fin m) :
    Fintype.card
        (V13RealLinearAdaptiveQRowGenerated
          (v13RealLinearUniformQRowExperiment observer) i₀) *
        2 ^ m ≤
      (2 * Fintype.card (Fin m)) *
        Fintype.card
          (V13RealLinearAdaptiveQRowWorld m (V13F2LinearEquiv m)) := by
  classical
  let G :=
    Fintype.card
      (V13RealLinearAdaptiveQRowGenerated
        (v13RealLinearUniformQRowExperiment observer) i₀)
  let R :=
    Fintype.card
      (V13RealLinearRowIndexedFixedTargetRowOccurrenceWorld m i₀)
  let A := Fintype.card (V13F2LinearEquiv m)
  let X := 2 ^ m
  let N := Fintype.card (Fin m)
  have hG : G ≤ R := by
    simpa [G, R] using
      v13RealLinearUniformOneRowGenerated_card_le_rowIndexedFixedOccurrence
        observer i₀
  have hR : R ≤ N * (2 * A) := by
    simpa [R, N, A] using
      v13RealLinearRowIndexedFixedTargetRowOccurrenceWorld_card_le i₀
  have hworld :
      Fintype.card
          (V13RealLinearAdaptiveQRowWorld m (V13F2LinearEquiv m)) =
        A * X := by
    dsimp [V13RealLinearAdaptiveQRowWorld, A, X]
    rw [Fintype.card_prod, v13RealLinear_f2vec_card]
  calc
    G * X ≤ (N * (2 * A)) * X :=
      Nat.mul_le_mul_right X (hG.trans hR)
    _ = (2 * N) * (A * X) := by ring
    _ =
        (2 * Fintype.card (Fin m)) *
          Fintype.card
            (V13RealLinearAdaptiveQRowWorld m (V13F2LinearEquiv m)) := by
      simp [N, A, X, hworld]

theorem v13RealLinearUniformCausalOneRowGenerated_counting_with_rowFactor
    {m : Nat} (observer : V13RealLinearCausalRowObserver m 1)
    (i₀ : Fin m) :
    Fintype.card
        (V13RealLinearAdaptiveQRowGenerated
          (v13RealLinearUniformCausalQRowExperiment observer) i₀) *
        2 ^ m ≤
      (2 * Fintype.card (Fin m)) *
        Fintype.card
          (V13RealLinearAdaptiveQRowWorld m (V13F2LinearEquiv m)) := by
  change
    Fintype.card
        (V13RealLinearAdaptiveQRowGenerated
          (v13RealLinearUniformQRowExperiment observer.toAdaptive) i₀) *
        2 ^ m ≤
      (2 * Fintype.card (Fin m)) *
        Fintype.card
          (V13RealLinearAdaptiveQRowWorld m (V13F2LinearEquiv m))
  exact
    v13RealLinearUniformOneRowGenerated_counting_with_rowFactor
      observer.toAdaptive i₀

/-- The row/bit transcript cylinders that are actually hit by generated
one-row worlds for a fixed observer.  Bounding this finite index set is exactly
the multiplicity left after the fixed-cylinder count. -/
def V13RealLinearUniformOneRowGeneratedCylinderIndex
    {m : Nat} (observer : V13RealLinearAdaptiveRowObserver m 1)
    (i₀ : Fin m) :=
  {idx : Fin m × ZMod 2 //
    ∃ omega : V13RealLinearAdaptiveQRowWorld m (V13F2LinearEquiv m),
      (v13RealLinearUniformQRowExperiment observer).generated i₀ omega ∧
        (v13RealLinearUniformQRowExperiment observer).branchRows omega =
          ({idx.1} : Finset (Fin m)) ∧
        idx.1 ∈ V13RealLinearTargetRows omega.1 i₀ ∧
        omega.2 i₀ = idx.2}

noncomputable instance {m : Nat}
    (observer : V13RealLinearAdaptiveRowObserver m 1) (i₀ : Fin m) :
    Fintype
      (V13RealLinearUniformOneRowGeneratedCylinderIndex observer i₀) := by
  classical
  unfold V13RealLinearUniformOneRowGeneratedCylinderIndex
  infer_instance

/-- Rows that occur in the active generated row/bit cylinder index.  This
forgets the target bit and isolates the row-choice part of the q = 1
obstruction. -/
def V13RealLinearUniformOneRowGeneratedRowIndex
    {m : Nat} (observer : V13RealLinearAdaptiveRowObserver m 1)
    (i₀ : Fin m) :=
  {row : Fin m //
    ∃ idx : V13RealLinearUniformOneRowGeneratedCylinderIndex observer i₀,
      idx.val.1 = row}

noncomputable instance {m : Nat}
    (observer : V13RealLinearAdaptiveRowObserver m 1) (i₀ : Fin m) :
    Fintype
      (V13RealLinearUniformOneRowGeneratedRowIndex observer i₀) := by
  classical
  unfold V13RealLinearUniformOneRowGeneratedRowIndex
  infer_instance

theorem v13RealLinearUniformCausalOneRow_branchRows_ne_empty_of_singletonWitness
    {m : Nat} (observer : V13RealLinearCausalRowObserver m 1)
    (rest omega : V13RealLinearAdaptiveQRowWorld m (V13F2LinearEquiv m))
    (row : Fin m)
    (homegaRows :
      (v13RealLinearUniformCausalQRowExperiment observer).branchRows omega =
        ({row} : Finset (Fin m))) :
    (v13RealLinearUniformCausalQRowExperiment observer).branchRows rest ≠
      ∅ := by
  classical
  intro hrestRows
  let E := v13RealLinearUniformCausalQRowExperiment observer
  let publicRest :=
    v13RealLinearPublicInput (E.world rest)
  let publicOmega :=
    v13RealLinearPublicInput (E.world omega)
  have hobserverRestRows :
      observer.rows (observer.branch publicRest) = ∅ := by
    simpa [E, publicRest, v13RealLinearUniformCausalQRowExperiment,
      v13RealLinearUniformQRowExperiment,
      V13RealLinearAdaptiveQRowExperiment.branchRows,
      V13RealLinearAdaptiveQRowExperiment.branch,
      V13RealLinearCausalRowObserver.toAdaptive,
      V13RealLinearCausalRowObserver.staticBranch] using hrestRows
  have hsame :
      v13RealLinearRowsTranscript
          (observer.rows (observer.branch publicRest)) publicRest =
        v13RealLinearRowsTranscript
          (observer.rows (observer.branch publicRest)) publicOmega := by
    funext row'
    have hmemEmpty : row'.val ∈ (∅ : Finset (Fin m)) := by
      rw [← hobserverRestRows]
      exact row'.property
    simp at hmemEmpty
  have hbranch :
      observer.branch publicOmega = observer.branch publicRest :=
    observer.branch_eq_of_same_branchRowsTranscript publicRest publicOmega
      hsame
  have hrowsEq :
      observer.rows (observer.branch publicOmega) =
        observer.rows (observer.branch publicRest) :=
    congrArg observer.rows hbranch
  have homegaObserverRows :
      observer.rows (observer.branch publicOmega) =
        ({row} : Finset (Fin m)) := by
    simpa [E, publicOmega, v13RealLinearUniformCausalQRowExperiment,
      v13RealLinearUniformQRowExperiment,
      V13RealLinearAdaptiveQRowExperiment.branchRows,
      V13RealLinearAdaptiveQRowExperiment.branch,
      V13RealLinearCausalRowObserver.toAdaptive,
      V13RealLinearCausalRowObserver.staticBranch] using homegaRows
  have hsingletonEmpty :
      ({row} : Finset (Fin m)) = ∅ := by
    rw [← homegaObserverRows, hrowsEq, hobserverRestRows]
  have hmem : row ∈ ({row} : Finset (Fin m)) := by simp
  rw [hsingletonEmpty] at hmem
  simp at hmem

theorem v13RealLinearUniformCausalOneRow_branchRows_ne_empty_of_activeRowIndex
    {m : Nat} (observer : V13RealLinearCausalRowObserver m 1)
    (i₀ : Fin m)
    (rest : V13RealLinearAdaptiveQRowWorld m (V13F2LinearEquiv m))
    (_activeRow :
      V13RealLinearUniformOneRowGeneratedRowIndex observer.toAdaptive i₀) :
    (v13RealLinearUniformCausalQRowExperiment observer).branchRows rest ≠
      ∅ := by
  classical
  rcases _activeRow.property with ⟨idx, _hidx⟩
  rcases idx.property with
    ⟨omega, _hgen, homegaRows, _htarget, _hbit⟩
  exact
    v13RealLinearUniformCausalOneRow_branchRows_ne_empty_of_singletonWitness
      observer rest omega idx.val.1 homegaRows

theorem v13RealLinearUniformCausalOneRow_branchRows_eq_singleton_of_activeRowIndex
    {m : Nat} (observer : V13RealLinearCausalRowObserver m 1)
    (i₀ : Fin m)
    (rest : V13RealLinearAdaptiveQRowWorld m (V13F2LinearEquiv m))
    (activeRow :
      V13RealLinearUniformOneRowGeneratedRowIndex observer.toAdaptive i₀) :
    ∃ row : Fin m,
      (v13RealLinearUniformCausalQRowExperiment observer).branchRows rest =
        ({row} : Finset (Fin m)) := by
  classical
  let E := v13RealLinearUniformCausalQRowExperiment observer
  have hcard : (E.branchRows rest).card ≤ 1 := E.branchRows_card_le rest
  have hne : E.branchRows rest ≠ ∅ :=
    v13RealLinearUniformCausalOneRow_branchRows_ne_empty_of_activeRowIndex
      observer i₀ rest activeRow
  have hcardNe : (E.branchRows rest).card ≠ 0 := by
    intro hzero
    exact hne (Finset.card_eq_zero.mp hzero)
  have hcardOne : (E.branchRows rest).card = 1 := by omega
  exact Finset.card_eq_one.mp hcardOne

theorem v13RealLinearNoTargetRowShear_not_generated_one_budget
    {m : Nat} (observer : V13RealLinearCausalRowObserver m 1)
    (i₀ : Fin m) (hm : 1 < m) (x : F2Vec m) :
    ¬ (v13RealLinearUniformCausalQRowExperiment observer).generated i₀
        (v13RealLinearNoTargetRowShear i₀ hm, x) := by
  exact
    (v13RealLinearUniformCausalQRowExperiment observer).not_generated_of_targetRows_empty
      i₀ (v13RealLinearNoTargetRowShear i₀ hm, x)
      (v13RealLinearNoTargetRowShear_targetRows_empty i₀ hm)

theorem v13RealLinearNoTargetRowShear_branchRows_eq_singleton_of_activeRowIndex
    {m : Nat} (observer : V13RealLinearCausalRowObserver m 1)
    (i₀ : Fin m) (hm : 1 < m) (x : F2Vec m)
    (activeRow :
      V13RealLinearUniformOneRowGeneratedRowIndex observer.toAdaptive i₀) :
    ∃ row : Fin m,
      (v13RealLinearUniformCausalQRowExperiment observer).branchRows
          (v13RealLinearNoTargetRowShear i₀ hm, x) =
        ({row} : Finset (Fin m)) :=
  v13RealLinearUniformCausalOneRow_branchRows_eq_singleton_of_activeRowIndex
    observer i₀ (v13RealLinearNoTargetRowShear i₀ hm, x) activeRow

/-- The all-dimensional singleton-rest bridge left by the no-target shear
reduction.  It says that a causal one-row observer cannot simultaneously have
an active generated singleton row `r` and put the explicit no-target rest world
in a different singleton branch row `s`. -/
def V13RealLinearUniformCausalOneRowNoTargetRestMismatchExclusion : Prop :=
  ∀ {m : Nat} (observer : V13RealLinearCausalRowObserver m 1)
    (i₀ : Fin m) (hm : 1 < m) (x : F2Vec m)
    (activeRow :
      V13RealLinearUniformOneRowGeneratedRowIndex observer.toAdaptive i₀)
    (restRow : Fin m),
    activeRow.val ≠ restRow →
      (v13RealLinearUniformCausalQRowExperiment observer).branchRows
          (v13RealLinearNoTargetRowShear i₀ hm, x) ≠
        ({restRow} : Finset (Fin m))

theorem v13RealLinearUniformCausalOneRow_restActiveSingleton_collision_of_bridge
    {m : Nat} (observer : V13RealLinearCausalRowObserver m 1)
    (rest active bridge :
      V13RealLinearAdaptiveQRowWorld m (V13F2LinearEquiv m))
    (restRow activeRow : Fin m)
    (hrestRows :
      (v13RealLinearUniformCausalQRowExperiment observer).branchRows rest =
        ({restRow} : Finset (Fin m)))
    (hactiveRows :
      (v13RealLinearUniformCausalQRowExperiment observer).branchRows active =
        ({activeRow} : Finset (Fin m)))
    (hrestSame :
      v13RealLinearRowsTranscript ({restRow} : Finset (Fin m))
          (v13RealLinearPublicInput
            ((v13RealLinearUniformCausalQRowExperiment observer).world rest)) =
        v13RealLinearRowsTranscript ({restRow} : Finset (Fin m))
          (v13RealLinearPublicInput
            ((v13RealLinearUniformCausalQRowExperiment observer).world bridge)))
    (hactiveSame :
      v13RealLinearRowsTranscript ({activeRow} : Finset (Fin m))
          (v13RealLinearPublicInput
            ((v13RealLinearUniformCausalQRowExperiment observer).world active)) =
        v13RealLinearRowsTranscript ({activeRow} : Finset (Fin m))
          (v13RealLinearPublicInput
            ((v13RealLinearUniformCausalQRowExperiment observer).world bridge)))
    (hne : activeRow ≠ restRow) :
    False := by
  classical
  let E := v13RealLinearUniformCausalQRowExperiment observer
  let publicRest := v13RealLinearPublicInput (E.world rest)
  let publicActive := v13RealLinearPublicInput (E.world active)
  let publicBridge := v13RealLinearPublicInput (E.world bridge)
  have hrestObserverRows :
      observer.rows (observer.branch publicRest) =
        ({restRow} : Finset (Fin m)) := by
    simpa [E, publicRest, v13RealLinearUniformCausalQRowExperiment,
      v13RealLinearUniformQRowExperiment,
      V13RealLinearAdaptiveQRowExperiment.branchRows,
      V13RealLinearAdaptiveQRowExperiment.branch,
      V13RealLinearCausalRowObserver.toAdaptive,
      V13RealLinearCausalRowObserver.staticBranch] using hrestRows
  have hrestSameObserver :
      v13RealLinearRowsTranscript
          (observer.rows (observer.branch publicRest)) publicRest =
        v13RealLinearRowsTranscript
          (observer.rows (observer.branch publicRest)) publicBridge := by
    rw [hrestObserverRows]
    simpa [E, publicRest, publicBridge] using hrestSame
  have hbranchRest :
      observer.branch publicBridge = observer.branch publicRest :=
    observer.branch_eq_of_same_branchRowsTranscript publicRest publicBridge
      hrestSameObserver
  have hbridgeRowsRest :
      E.branchRows bridge = ({restRow} : Finset (Fin m)) := by
    have hrowsEq :
        observer.rows (observer.branch publicBridge) =
          observer.rows (observer.branch publicRest) :=
      congrArg observer.rows hbranchRest
    simpa [E, publicBridge, v13RealLinearUniformCausalQRowExperiment,
      v13RealLinearUniformQRowExperiment,
      V13RealLinearAdaptiveQRowExperiment.branchRows,
      V13RealLinearAdaptiveQRowExperiment.branch,
      V13RealLinearCausalRowObserver.toAdaptive,
      V13RealLinearCausalRowObserver.staticBranch] using
        hrowsEq.trans hrestObserverRows
  have hactiveObserverRows :
      observer.rows (observer.branch publicActive) =
        ({activeRow} : Finset (Fin m)) := by
    simpa [E, publicActive, v13RealLinearUniformCausalQRowExperiment,
      v13RealLinearUniformQRowExperiment,
      V13RealLinearAdaptiveQRowExperiment.branchRows,
      V13RealLinearAdaptiveQRowExperiment.branch,
      V13RealLinearCausalRowObserver.toAdaptive,
      V13RealLinearCausalRowObserver.staticBranch] using hactiveRows
  have hactiveSameObserver :
      v13RealLinearRowsTranscript
          (observer.rows (observer.branch publicActive)) publicActive =
        v13RealLinearRowsTranscript
          (observer.rows (observer.branch publicActive)) publicBridge := by
    rw [hactiveObserverRows]
    simpa [E, publicActive, publicBridge] using hactiveSame
  have hbranchActive :
      observer.branch publicBridge = observer.branch publicActive :=
    observer.branch_eq_of_same_branchRowsTranscript publicActive publicBridge
      hactiveSameObserver
  have hbridgeRowsActive :
      E.branchRows bridge = ({activeRow} : Finset (Fin m)) := by
    have hrowsEq :
        observer.rows (observer.branch publicBridge) =
          observer.rows (observer.branch publicActive) :=
      congrArg observer.rows hbranchActive
    simpa [E, publicBridge, v13RealLinearUniformCausalQRowExperiment,
      v13RealLinearUniformQRowExperiment,
      V13RealLinearAdaptiveQRowExperiment.branchRows,
      V13RealLinearAdaptiveQRowExperiment.branch,
      V13RealLinearCausalRowObserver.toAdaptive,
      V13RealLinearCausalRowObserver.staticBranch] using
        hrowsEq.trans hactiveObserverRows
  have hsingletons :
      ({restRow} : Finset (Fin m)) = ({activeRow} : Finset (Fin m)) :=
    hbridgeRowsRest.symm.trans hbridgeRowsActive
  have hmem : restRow ∈ ({activeRow} : Finset (Fin m)) := by
    rw [← hsingletons]
    simp
  have hrowEq : restRow = activeRow := by
    simpa using hmem
  exact hne hrowEq.symm

theorem v13RealLinearNoTargetRowShear_branchRows_ne_of_activeRowIndex_of_bridgeFamily
    {m : Nat} (observer : V13RealLinearCausalRowObserver m 1)
    (i₀ : Fin m) (hm : 1 < m) (x : F2Vec m)
    (activeRow :
      V13RealLinearUniformOneRowGeneratedRowIndex observer.toAdaptive i₀)
    (restRow : Fin m)
    (hneq : activeRow.val ≠ restRow)
    (bridge :
      ∀ active :
          V13RealLinearAdaptiveQRowWorld m (V13F2LinearEquiv m),
        (v13RealLinearUniformCausalQRowExperiment observer).branchRows active =
            ({activeRow.val} : Finset (Fin m)) →
        activeRow.val ∈ V13RealLinearTargetRows active.1 i₀ →
          V13RealLinearAdaptiveQRowWorld m (V13F2LinearEquiv m))
    (hbridge :
      ∀ (active :
          V13RealLinearAdaptiveQRowWorld m (V13F2LinearEquiv m))
        (hactiveRows :
          (v13RealLinearUniformCausalQRowExperiment observer).branchRows
              active =
            ({activeRow.val} : Finset (Fin m)))
        (htarget :
          activeRow.val ∈ V13RealLinearTargetRows active.1 i₀),
        v13RealLinearRowsTranscript ({restRow} : Finset (Fin m))
            (v13RealLinearPublicInput
              ((v13RealLinearUniformCausalQRowExperiment observer).world
                (v13RealLinearNoTargetRowShear i₀ hm, x))) =
          v13RealLinearRowsTranscript ({restRow} : Finset (Fin m))
            (v13RealLinearPublicInput
              ((v13RealLinearUniformCausalQRowExperiment observer).world
                (bridge active hactiveRows htarget))) ∧
          v13RealLinearRowsTranscript
              ({activeRow.val} : Finset (Fin m))
              (v13RealLinearPublicInput
                ((v13RealLinearUniformCausalQRowExperiment observer).world
                  active)) =
            v13RealLinearRowsTranscript
              ({activeRow.val} : Finset (Fin m))
              (v13RealLinearPublicInput
                ((v13RealLinearUniformCausalQRowExperiment observer).world
                  (bridge active hactiveRows htarget)))) :
    (v13RealLinearUniformCausalQRowExperiment observer).branchRows
        (v13RealLinearNoTargetRowShear i₀ hm, x) ≠
      ({restRow} : Finset (Fin m)) := by
  classical
  intro hrestRows
  rcases activeRow.property with ⟨idx, hidx⟩
  rcases idx.property with
    ⟨active, _hgen, hactiveRows, htarget, _hbit⟩
  have hidxRow : idx.val.1 = activeRow.val := hidx
  have hactiveRows' :
      (v13RealLinearUniformCausalQRowExperiment observer).branchRows active =
        ({activeRow.val} : Finset (Fin m)) := by
    simpa [v13RealLinearUniformCausalQRowExperiment, hidxRow] using hactiveRows
  have htarget' :
      activeRow.val ∈ V13RealLinearTargetRows active.1 i₀ := by
    simpa [hidxRow] using htarget
  obtain ⟨hrestSame, hactiveSame⟩ :=
    hbridge active hactiveRows' htarget'
  exact
    v13RealLinearUniformCausalOneRow_restActiveSingleton_collision_of_bridge
      observer (v13RealLinearNoTargetRowShear i₀ hm, x) active
      (bridge active hactiveRows' htarget') restRow activeRow.val hrestRows
      hactiveRows' hrestSame hactiveSame hneq

theorem v13RealLinearNoTargetRowShear_branchRows_ne_of_activeRowIndex_of_bridgeMapFamily
    {m : Nat} (observer : V13RealLinearCausalRowObserver m 1)
    (i₀ : Fin m) (hm : 1 < m) (x : F2Vec m)
    (activeRow :
      V13RealLinearUniformOneRowGeneratedRowIndex observer.toAdaptive i₀)
    (restRow : Fin m)
    (hneq : activeRow.val ≠ restRow)
    (bridgeMap :
      ∀ active :
          V13RealLinearAdaptiveQRowWorld m (V13F2LinearEquiv m),
        (v13RealLinearUniformCausalQRowExperiment observer).branchRows active =
            ({activeRow.val} : Finset (Fin m)) →
        activeRow.val ∈ V13RealLinearTargetRows active.1 i₀ →
          {bridgeA : V13F2LinearEquiv m //
            (∀ probe : F2Vec m,
              (v13RealLinearNoTargetRowShear i₀ hm).toEquiv probe restRow =
                bridgeA.toEquiv probe restRow) ∧
            (∀ probe : F2Vec m,
              active.1.toEquiv probe activeRow.val =
                bridgeA.toEquiv probe activeRow.val)}) :
    (v13RealLinearUniformCausalQRowExperiment observer).branchRows
        (v13RealLinearNoTargetRowShear i₀ hm, x) ≠
      ({restRow} : Finset (Fin m)) := by
  classical
  let bridge :
      ∀ active :
          V13RealLinearAdaptiveQRowWorld m (V13F2LinearEquiv m),
        (v13RealLinearUniformCausalQRowExperiment observer).branchRows active =
            ({activeRow.val} : Finset (Fin m)) →
        activeRow.val ∈ V13RealLinearTargetRows active.1 i₀ →
          V13RealLinearAdaptiveQRowWorld m (V13F2LinearEquiv m) :=
    fun active hactiveRows htarget =>
      let bridgeA := (bridgeMap active hactiveRows htarget).val
      let restBit :=
        (v13RealLinearNoTargetRowShear i₀ hm).toEquiv x restRow
      let targetBit := active.2 i₀
      let bridgeX :=
        Classical.choose
          (v13RealLinearNoTargetRowShear_exists_bridgeX_for_row_target_bits
            i₀ hm restRow restBit targetBit)
      (bridgeA, bridgeX)
  refine
    v13RealLinearNoTargetRowShear_branchRows_ne_of_activeRowIndex_of_bridgeFamily
      observer i₀ hm x activeRow restRow hneq bridge ?_
  intro active hactiveRows htarget
  let bridgeMapData := bridgeMap active hactiveRows htarget
  let bridgeA := bridgeMapData.val
  let restBit :=
    (v13RealLinearNoTargetRowShear i₀ hm).toEquiv x restRow
  let targetBit := active.2 i₀
  let bridgeX :=
    Classical.choose
      (v13RealLinearNoTargetRowShear_exists_bridgeX_for_row_target_bits
        i₀ hm restRow restBit targetBit)
  have hbridgeX :
      (v13RealLinearNoTargetRowShear i₀ hm).toEquiv bridgeX restRow =
          restBit ∧
        bridgeX i₀ = targetBit :=
    Classical.choose_spec
      (v13RealLinearNoTargetRowShear_exists_bridgeX_for_row_target_bits
        i₀ hm restRow restBit targetBit)
  have hrestFun :
      ∀ probe : F2Vec m,
        (v13RealLinearNoTargetRowShear i₀ hm).toEquiv probe restRow =
          bridgeA.toEquiv probe restRow :=
    bridgeMapData.property.1
  have hactiveFun :
      ∀ probe : F2Vec m,
        active.1.toEquiv probe activeRow.val =
          bridgeA.toEquiv probe activeRow.val :=
    bridgeMapData.property.2
  have htargetFun :
      ∀ probe : F2Vec m,
        active.1.toEquiv probe activeRow.val = probe i₀ :=
    (v13RealLinear_mem_targetRows_iff active.1 i₀ activeRow.val).1 htarget
  have hrestBit :
      (v13RealLinearNoTargetRowShear i₀ hm).toEquiv x restRow =
        bridgeA.toEquiv bridgeX restRow := by
    calc
      (v13RealLinearNoTargetRowShear i₀ hm).toEquiv x restRow = restBit := rfl
      _ = (v13RealLinearNoTargetRowShear i₀ hm).toEquiv bridgeX restRow :=
        hbridgeX.1.symm
      _ = bridgeA.toEquiv bridgeX restRow := hrestFun bridgeX
  have hactiveBit :
      active.1.toEquiv active.2 activeRow.val =
        bridgeA.toEquiv bridgeX activeRow.val := by
    calc
      active.1.toEquiv active.2 activeRow.val = active.2 i₀ :=
        htargetFun active.2
      _ = bridgeX i₀ := hbridgeX.2.symm
      _ = active.1.toEquiv bridgeX activeRow.val := (htargetFun bridgeX).symm
      _ = bridgeA.toEquiv bridgeX activeRow.val := hactiveFun bridgeX
  simpa [v13RealLinearUniformCausalQRowExperiment,
    v13RealLinearUniformQRowExperiment, V13RealLinearAdaptiveQRowExperiment.world,
    bridge, bridgeMapData, bridgeA, bridgeX, restBit, targetBit] using
    v13RealLinearNoTargetRowShear_bridgeTranscripts_of_row_matches
      i₀ hm x active.2 bridgeX active.1 bridgeA restRow activeRow.val
      hrestFun hrestBit hactiveFun hactiveBit

theorem v13RealLinearNoTargetRowShear_branchRows_ne_of_activeRowIndex
    {m : Nat} (observer : V13RealLinearCausalRowObserver m 1)
    (i₀ : Fin m) (hm : 1 < m) (x : F2Vec m)
    (activeRow :
      V13RealLinearUniformOneRowGeneratedRowIndex observer.toAdaptive i₀)
    (restRow : Fin m)
    (hneq : activeRow.val ≠ restRow) :
    (v13RealLinearUniformCausalQRowExperiment observer).branchRows
        (v13RealLinearNoTargetRowShear i₀ hm, x) ≠
      ({restRow} : Finset (Fin m)) := by
  classical
  refine
    v13RealLinearNoTargetRowShear_branchRows_ne_of_activeRowIndex_of_bridgeMapFamily
      observer i₀ hm x activeRow restRow hneq ?_
  intro active _hactiveRows htarget
  let bridgeExists :=
    v13RealLinearNoTargetRowShear_exists_bridgeMap_for_rows
      i₀ hm restRow activeRow.val hneq
  let bridgeA : V13F2LinearEquiv m := Classical.choose bridgeExists
  have hbridgeA :
      (∀ probe : F2Vec m,
        (v13RealLinearNoTargetRowShear i₀ hm).toEquiv probe restRow =
          bridgeA.toEquiv probe restRow) ∧
      (∀ probe : F2Vec m,
        bridgeA.toEquiv probe activeRow.val = probe i₀) :=
    Classical.choose_spec bridgeExists
  have hrestFun :
      ∀ probe : F2Vec m,
        (v13RealLinearNoTargetRowShear i₀ hm).toEquiv probe restRow =
          bridgeA.toEquiv probe restRow :=
    hbridgeA.1
  have hactiveTargetFun :
      ∀ probe : F2Vec m,
        bridgeA.toEquiv probe activeRow.val = probe i₀ :=
    hbridgeA.2
  refine ⟨bridgeA, hrestFun, ?_⟩
  intro probe
  have htargetFun :
      active.1.toEquiv probe activeRow.val = probe i₀ :=
    (v13RealLinear_mem_targetRows_iff active.1 i₀ activeRow.val).1
      htarget probe
  exact htargetFun.trans (hactiveTargetFun probe).symm

theorem V13RealLinearUniformCausalOneRowNoTargetRestMismatchExclusion_proved :
    V13RealLinearUniformCausalOneRowNoTargetRestMismatchExclusion := by
  intro m observer i₀ hm x activeRow restRow hneq
  exact
    v13RealLinearNoTargetRowShear_branchRows_ne_of_activeRowIndex
      observer i₀ hm x activeRow restRow hneq

theorem v13RealLinearSwapShear10_branchRows_ne_empty_of_activeRowIndex
    (observer : V13RealLinearCausalRowObserver 2 1) (x : F2Vec 2)
    (activeRow :
      V13RealLinearUniformOneRowGeneratedRowIndex
        observer.toAdaptive (0 : Fin 2)) :
    (v13RealLinearUniformCausalQRowExperiment observer).branchRows
        (v13RealLinearSwapShear10, x) ≠ ∅ := by
  classical
  rcases activeRow.property with ⟨idx, _hidx⟩
  rcases idx.property with
    ⟨omega, _hgen, homegaRows, _htarget, _hbit⟩
  exact
    v13RealLinearSwapShear10_branchRows_ne_empty_of_singletonWitness
      observer x omega idx.val.1 homegaRows

theorem v13RealLinearSwapShear10_branchRows_ne_zero_of_activeRowOne
    (observer : V13RealLinearCausalRowObserver 2 1) (x : F2Vec 2)
    (activeRow :
      V13RealLinearUniformOneRowGeneratedRowIndex
        observer.toAdaptive (0 : Fin 2))
    (hrow : activeRow.val = (1 : Fin 2)) :
    (v13RealLinearUniformCausalQRowExperiment observer).branchRows
        (v13RealLinearSwapShear10, x) ≠
      ({(0 : Fin 2)} : Finset (Fin 2)) := by
  classical
  rcases activeRow.property with ⟨idx, hidx⟩
  rcases idx.property with
    ⟨omega, _hgen, homegaRows, htarget, _hbit⟩
  have hidxRow : idx.val.1 = (1 : Fin 2) := by
    exact hidx.trans hrow
  have homegaRowsOne :
      (v13RealLinearUniformCausalQRowExperiment observer).branchRows omega =
        ({(1 : Fin 2)} : Finset (Fin 2)) := by
    simpa [v13RealLinearUniformCausalQRowExperiment, hidxRow] using homegaRows
  have htargetOne :
      (1 : Fin 2) ∈ V13RealLinearTargetRows omega.1 (0 : Fin 2) := by
    simpa [hidxRow] using htarget
  exact
    v13RealLinearSwapShear10_branchRows_ne_zero_of_singletonOneWitness
      observer x omega homegaRowsOne htargetOne

theorem v13RealLinearSwapShear10_branchRows_ne_one_of_activeRowZero
    (observer : V13RealLinearCausalRowObserver 2 1) (x : F2Vec 2)
    (activeRow :
      V13RealLinearUniformOneRowGeneratedRowIndex
        observer.toAdaptive (0 : Fin 2))
    (hrow : activeRow.val = (0 : Fin 2)) :
    (v13RealLinearUniformCausalQRowExperiment observer).branchRows
        (v13RealLinearSwapShear10, x) ≠
      ({(1 : Fin 2)} : Finset (Fin 2)) := by
  classical
  rcases activeRow.property with ⟨idx, hidx⟩
  rcases idx.property with
    ⟨omega, _hgen, homegaRows, htarget, _hbit⟩
  have hidxRow : idx.val.1 = (0 : Fin 2) := by
    exact hidx.trans hrow
  have homegaRowsZero :
      (v13RealLinearUniformCausalQRowExperiment observer).branchRows omega =
        ({(0 : Fin 2)} : Finset (Fin 2)) := by
    simpa [v13RealLinearUniformCausalQRowExperiment, hidxRow] using homegaRows
  have htargetZero :
      (0 : Fin 2) ∈ V13RealLinearTargetRows omega.1 (0 : Fin 2) := by
    simpa [hidxRow] using htarget
  exact
    v13RealLinearSwapShear10_branchRows_ne_one_of_singletonZeroWitness
      observer x omega homegaRowsZero htargetZero

theorem v13RealLinearUniformCausalOneRowActiveRowPairExclusion_two_zero
    (observer : V13RealLinearCausalRowObserver 2 1)
    (row₀ row₁ :
      V13RealLinearUniformOneRowGeneratedRowIndex
        observer.toAdaptive (0 : Fin 2)) :
    row₀.val = row₁.val := by
  classical
  have hfin : ∀ r : Fin 2, r = (0 : Fin 2) ∨ r = (1 : Fin 2) := by
    intro r
    fin_cases r <;> simp
  rcases hfin row₀.val with hrow₀zero | hrow₀one
  · rcases hfin row₁.val with hrow₁zero | hrow₁one
    · rw [hrow₀zero, hrow₁zero]
    · let x : F2Vec 2 := fun _ => 0
      have hcases := v13RealLinearSwapShear10_branchRows_cases observer x
      rcases hcases with hempty | hrest
      · exact False.elim
          (v13RealLinearSwapShear10_branchRows_ne_empty_of_activeRowIndex
            observer x row₀ hempty)
      · rcases hrest with hzero | hone
        · exact False.elim
            (v13RealLinearSwapShear10_branchRows_ne_zero_of_activeRowOne
              observer x row₁ hrow₁one hzero)
        · exact False.elim
            (v13RealLinearSwapShear10_branchRows_ne_one_of_activeRowZero
              observer x row₀ hrow₀zero hone)
  · rcases hfin row₁.val with hrow₁zero | hrow₁one
    · let x : F2Vec 2 := fun _ => 0
      have hcases := v13RealLinearSwapShear10_branchRows_cases observer x
      rcases hcases with hempty | hrest
      · exact False.elim
          (v13RealLinearSwapShear10_branchRows_ne_empty_of_activeRowIndex
            observer x row₀ hempty)
      · rcases hrest with hzero | hone
        · exact False.elim
            (v13RealLinearSwapShear10_branchRows_ne_zero_of_activeRowOne
              observer x row₀ hrow₀one hzero)
        · exact False.elim
            (v13RealLinearSwapShear10_branchRows_ne_one_of_activeRowZero
              observer x row₁ hrow₁zero hone)
    · rw [hrow₀one, hrow₁one]

theorem v13RealLinearShear01_branchRows_ne_empty_of_singletonWitness_one
    (observer : V13RealLinearCausalRowObserver 2 1) (x : F2Vec 2)
    (omega : V13RealLinearAdaptiveQRowWorld 2 (V13F2LinearEquiv 2))
    (row : Fin 2)
    (homegaRows :
      (v13RealLinearUniformCausalQRowExperiment observer).branchRows omega =
        ({row} : Finset (Fin 2))) :
    (v13RealLinearUniformCausalQRowExperiment observer).branchRows
        (v13RealLinearShear01, x) ≠ ∅ := by
  classical
  intro hrestRows
  let E := v13RealLinearUniformCausalQRowExperiment observer
  let rest : V13RealLinearAdaptiveQRowWorld 2 (V13F2LinearEquiv 2) :=
    (v13RealLinearShear01, x)
  let publicRest :=
    v13RealLinearPublicInput (E.world rest)
  let publicOmega :=
    v13RealLinearPublicInput (E.world omega)
  have hobserverRestRows :
      observer.rows (observer.branch publicRest) = ∅ := by
    simpa [E, rest, publicRest, v13RealLinearUniformCausalQRowExperiment,
      v13RealLinearUniformQRowExperiment,
      V13RealLinearAdaptiveQRowExperiment.branchRows,
      V13RealLinearAdaptiveQRowExperiment.branch,
      V13RealLinearCausalRowObserver.toAdaptive,
      V13RealLinearCausalRowObserver.staticBranch] using hrestRows
  have hsame :
      v13RealLinearRowsTranscript
          (observer.rows (observer.branch publicRest)) publicRest =
        v13RealLinearRowsTranscript
          (observer.rows (observer.branch publicRest)) publicOmega := by
    funext row
    have hmemEmpty : row.val ∈ (∅ : Finset (Fin 2)) := by
      rw [← hobserverRestRows]
      exact row.property
    simp at hmemEmpty
  have hbranch :
      observer.branch publicOmega = observer.branch publicRest :=
    observer.branch_eq_of_same_branchRowsTranscript publicRest publicOmega
      hsame
  have hrowsEq :
      observer.rows (observer.branch publicOmega) =
        observer.rows (observer.branch publicRest) :=
    congrArg observer.rows hbranch
  have homegaObserverRows :
      observer.rows (observer.branch publicOmega) =
        ({row} : Finset (Fin 2)) := by
    simpa [E, publicOmega, v13RealLinearUniformCausalQRowExperiment,
      v13RealLinearUniformQRowExperiment,
      V13RealLinearAdaptiveQRowExperiment.branchRows,
      V13RealLinearAdaptiveQRowExperiment.branch,
      V13RealLinearCausalRowObserver.toAdaptive,
      V13RealLinearCausalRowObserver.staticBranch] using homegaRows
  have hsingletonEmpty :
      ({row} : Finset (Fin 2)) = ∅ := by
    rw [← homegaObserverRows, hrowsEq, hobserverRestRows]
  have hmem : row ∈ ({row} : Finset (Fin 2)) := by simp
  rw [hsingletonEmpty] at hmem
  simp at hmem

theorem v13RealLinearShear01_branchRows_ne_zero_of_singletonOneWitness_one
    (observer : V13RealLinearCausalRowObserver 2 1) (x : F2Vec 2)
    (omega : V13RealLinearAdaptiveQRowWorld 2 (V13F2LinearEquiv 2))
    (homegaRows :
      (v13RealLinearUniformCausalQRowExperiment observer).branchRows omega =
        ({(1 : Fin 2)} : Finset (Fin 2)))
    (htarget :
      (1 : Fin 2) ∈ V13RealLinearTargetRows omega.1 (1 : Fin 2)) :
    (v13RealLinearUniformCausalQRowExperiment observer).branchRows
        (v13RealLinearShear01, x) ≠
      ({(0 : Fin 2)} : Finset (Fin 2)) := by
  classical
  intro hrestRows
  let E := v13RealLinearUniformCausalQRowExperiment observer
  let rest : V13RealLinearAdaptiveQRowWorld 2 (V13F2LinearEquiv 2) :=
    (v13RealLinearShear01, x)
  let bridgeX : F2Vec 2 :=
    fun r => if r = (0 : Fin 2) then x (0 : Fin 2) else omega.2 (1 : Fin 2)
  let bridge : V13RealLinearAdaptiveQRowWorld 2 (V13F2LinearEquiv 2) :=
    (v13RealLinearIdentity 2, bridgeX)
  let publicRest := v13RealLinearPublicInput (E.world rest)
  let publicBridge := v13RealLinearPublicInput (E.world bridge)
  let publicOmega := v13RealLinearPublicInput (E.world omega)
  have hrestObserverRows :
      observer.rows (observer.branch publicRest) =
        ({(0 : Fin 2)} : Finset (Fin 2)) := by
    simpa [E, rest, publicRest, v13RealLinearUniformCausalQRowExperiment,
      v13RealLinearUniformQRowExperiment,
      V13RealLinearAdaptiveQRowExperiment.branchRows,
      V13RealLinearAdaptiveQRowExperiment.branch,
      V13RealLinearCausalRowObserver.toAdaptive,
      V13RealLinearCausalRowObserver.staticBranch] using hrestRows
  have hsameRest :
      v13RealLinearRowsTranscript
          (observer.rows (observer.branch publicRest)) publicRest =
        v13RealLinearRowsTranscript
          (observer.rows (observer.branch publicRest)) publicBridge := by
    rw [hrestObserverRows]
    funext row
    rcases row with ⟨row, hrow⟩
    have hrow0 : row = (0 : Fin 2) := by
      simpa using hrow
    subst row
    apply Prod.ext
    · funext probe
      change
        v13RealLinearShear01.toEquiv probe (0 : Fin 2) =
          (v13RealLinearIdentity 2).toEquiv probe (0 : Fin 2)
      simp [v13RealLinearShear01, v13RealLinearIdentity]
    · change
        v13RealLinearShear01.toEquiv x (0 : Fin 2) =
          (v13RealLinearIdentity 2).toEquiv bridgeX (0 : Fin 2)
      simp [v13RealLinearShear01, v13RealLinearIdentity, bridgeX]
  have hbranchRest :
      observer.branch publicBridge = observer.branch publicRest :=
    observer.branch_eq_of_same_branchRowsTranscript publicRest publicBridge
      hsameRest
  have hbridgeRowsZero :
      E.branchRows bridge = ({(0 : Fin 2)} : Finset (Fin 2)) := by
    have hrowsEq :
        observer.rows (observer.branch publicBridge) =
          observer.rows (observer.branch publicRest) :=
      congrArg observer.rows hbranchRest
    simpa [E, bridge, publicBridge, v13RealLinearUniformCausalQRowExperiment,
      v13RealLinearUniformQRowExperiment,
      V13RealLinearAdaptiveQRowExperiment.branchRows,
      V13RealLinearAdaptiveQRowExperiment.branch,
      V13RealLinearCausalRowObserver.toAdaptive,
      V13RealLinearCausalRowObserver.staticBranch] using
        hrowsEq.trans hrestObserverRows
  have homegaObserverRows :
      observer.rows (observer.branch publicOmega) =
        ({(1 : Fin 2)} : Finset (Fin 2)) := by
    simpa [E, publicOmega, v13RealLinearUniformCausalQRowExperiment,
      v13RealLinearUniformQRowExperiment,
      V13RealLinearAdaptiveQRowExperiment.branchRows,
      V13RealLinearAdaptiveQRowExperiment.branch,
      V13RealLinearCausalRowObserver.toAdaptive,
      V13RealLinearCausalRowObserver.staticBranch] using homegaRows
  have htargetFun :
      ∀ probe : F2Vec 2, omega.1.toEquiv probe (1 : Fin 2) =
        probe (1 : Fin 2) :=
    (v13RealLinear_mem_targetRows_iff omega.1 (1 : Fin 2) (1 : Fin 2)).1
      htarget
  have hsameOmega :
      v13RealLinearRowsTranscript
          (observer.rows (observer.branch publicOmega)) publicOmega =
        v13RealLinearRowsTranscript
          (observer.rows (observer.branch publicOmega)) publicBridge := by
    rw [homegaObserverRows]
    funext row
    rcases row with ⟨row, hrow⟩
    have hrow1 : row = (1 : Fin 2) := by
      simpa using hrow
    subst row
    apply Prod.ext
    · funext probe
      change
        omega.1.toEquiv probe (1 : Fin 2) =
          (v13RealLinearIdentity 2).toEquiv probe (1 : Fin 2)
      rw [htargetFun probe]
      simp [v13RealLinearIdentity]
    · have htargetX := htargetFun omega.2
      change
        omega.1.toEquiv omega.2 (1 : Fin 2) =
          (v13RealLinearIdentity 2).toEquiv bridgeX (1 : Fin 2)
      rw [htargetX]
      simp [v13RealLinearIdentity, bridgeX]
  have hbranchOmega :
      observer.branch publicBridge = observer.branch publicOmega :=
    observer.branch_eq_of_same_branchRowsTranscript publicOmega publicBridge
      hsameOmega
  have hbridgeRowsOne :
      E.branchRows bridge = ({(1 : Fin 2)} : Finset (Fin 2)) := by
    have hrowsEq :
        observer.rows (observer.branch publicBridge) =
          observer.rows (observer.branch publicOmega) :=
      congrArg observer.rows hbranchOmega
    simpa [E, bridge, publicBridge, v13RealLinearUniformCausalQRowExperiment,
      v13RealLinearUniformQRowExperiment,
      V13RealLinearAdaptiveQRowExperiment.branchRows,
      V13RealLinearAdaptiveQRowExperiment.branch,
      V13RealLinearCausalRowObserver.toAdaptive,
      V13RealLinearCausalRowObserver.staticBranch] using
        hrowsEq.trans homegaObserverRows
  have hzeroOne :
      ({(0 : Fin 2)} : Finset (Fin 2)) =
        ({(1 : Fin 2)} : Finset (Fin 2)) :=
    hbridgeRowsZero.symm.trans hbridgeRowsOne
  have hmem : (0 : Fin 2) ∈ ({(1 : Fin 2)} : Finset (Fin 2)) := by
    rw [← hzeroOne]
    simp
  simp at hmem

theorem v13RealLinearShear01_branchRows_ne_one_of_singletonZeroWitness_one
    (observer : V13RealLinearCausalRowObserver 2 1) (x : F2Vec 2)
    (omega : V13RealLinearAdaptiveQRowWorld 2 (V13F2LinearEquiv 2))
    (homegaRows :
      (v13RealLinearUniformCausalQRowExperiment observer).branchRows omega =
        ({(0 : Fin 2)} : Finset (Fin 2)))
    (htarget :
      (0 : Fin 2) ∈ V13RealLinearTargetRows omega.1 (1 : Fin 2)) :
    (v13RealLinearUniformCausalQRowExperiment observer).branchRows
        (v13RealLinearShear01, x) ≠
      ({(1 : Fin 2)} : Finset (Fin 2)) := by
  classical
  intro hrestRows
  let E := v13RealLinearUniformCausalQRowExperiment observer
  let rest : V13RealLinearAdaptiveQRowWorld 2 (V13F2LinearEquiv 2) :=
    (v13RealLinearShear01, x)
  let bridgeX : F2Vec 2 :=
    fun r =>
      if r = (1 : Fin 2) then omega.2 (1 : Fin 2)
      else omega.2 (1 : Fin 2) + (x (0 : Fin 2) + x (1 : Fin 2))
  let bridge : V13RealLinearAdaptiveQRowWorld 2 (V13F2LinearEquiv 2) :=
    (v13RealLinearSwapShear10, bridgeX)
  let publicRest := v13RealLinearPublicInput (E.world rest)
  let publicBridge := v13RealLinearPublicInput (E.world bridge)
  let publicOmega := v13RealLinearPublicInput (E.world omega)
  have hrestObserverRows :
      observer.rows (observer.branch publicRest) =
        ({(1 : Fin 2)} : Finset (Fin 2)) := by
    simpa [E, rest, publicRest, v13RealLinearUniformCausalQRowExperiment,
      v13RealLinearUniformQRowExperiment,
      V13RealLinearAdaptiveQRowExperiment.branchRows,
      V13RealLinearAdaptiveQRowExperiment.branch,
      V13RealLinearCausalRowObserver.toAdaptive,
      V13RealLinearCausalRowObserver.staticBranch] using hrestRows
  have hsameRest :
      v13RealLinearRowsTranscript
          (observer.rows (observer.branch publicRest)) publicRest =
        v13RealLinearRowsTranscript
          (observer.rows (observer.branch publicRest)) publicBridge := by
    rw [hrestObserverRows]
    funext row
    rcases row with ⟨row, hrow⟩
    have hrow1 : row = (1 : Fin 2) := by
      simpa using hrow
    subst row
    apply Prod.ext
    · funext probe
      change
        v13RealLinearShear01.toEquiv probe (1 : Fin 2) =
          v13RealLinearSwapShear10.toEquiv probe (1 : Fin 2)
      simp [v13RealLinearShear01, v13RealLinearSwapShear10]
    · change
        v13RealLinearShear01.toEquiv x (1 : Fin 2) =
          v13RealLinearSwapShear10.toEquiv bridgeX (1 : Fin 2)
      simp [v13RealLinearShear01, v13RealLinearSwapShear10, bridgeX,
        add_assoc, add_left_comm, add_comm]
      simpa using f2_add_right_self (0 : ZMod 2) (omega.2 (1 : Fin 2))
  have hbranchRest :
      observer.branch publicBridge = observer.branch publicRest :=
    observer.branch_eq_of_same_branchRowsTranscript publicRest publicBridge
      hsameRest
  have hbridgeRowsOne :
      E.branchRows bridge = ({(1 : Fin 2)} : Finset (Fin 2)) := by
    have hrowsEq :
        observer.rows (observer.branch publicBridge) =
          observer.rows (observer.branch publicRest) :=
      congrArg observer.rows hbranchRest
    simpa [E, bridge, publicBridge, v13RealLinearUniformCausalQRowExperiment,
      v13RealLinearUniformQRowExperiment,
      V13RealLinearAdaptiveQRowExperiment.branchRows,
      V13RealLinearAdaptiveQRowExperiment.branch,
      V13RealLinearCausalRowObserver.toAdaptive,
      V13RealLinearCausalRowObserver.staticBranch] using
        hrowsEq.trans hrestObserverRows
  have homegaObserverRows :
      observer.rows (observer.branch publicOmega) =
        ({(0 : Fin 2)} : Finset (Fin 2)) := by
    simpa [E, publicOmega, v13RealLinearUniformCausalQRowExperiment,
      v13RealLinearUniformQRowExperiment,
      V13RealLinearAdaptiveQRowExperiment.branchRows,
      V13RealLinearAdaptiveQRowExperiment.branch,
      V13RealLinearCausalRowObserver.toAdaptive,
      V13RealLinearCausalRowObserver.staticBranch] using homegaRows
  have htargetFun :
      ∀ probe : F2Vec 2, omega.1.toEquiv probe (0 : Fin 2) =
        probe (1 : Fin 2) :=
    (v13RealLinear_mem_targetRows_iff omega.1 (1 : Fin 2) (0 : Fin 2)).1
      htarget
  have hsameOmega :
      v13RealLinearRowsTranscript
          (observer.rows (observer.branch publicOmega)) publicOmega =
        v13RealLinearRowsTranscript
          (observer.rows (observer.branch publicOmega)) publicBridge := by
    rw [homegaObserverRows]
    funext row
    rcases row with ⟨row, hrow⟩
    have hrow0 : row = (0 : Fin 2) := by
      simpa using hrow
    subst row
    apply Prod.ext
    · funext probe
      change
        omega.1.toEquiv probe (0 : Fin 2) =
          v13RealLinearSwapShear10.toEquiv probe (0 : Fin 2)
      rw [htargetFun probe]
      simp [v13RealLinearSwapShear10]
    · have htargetX := htargetFun omega.2
      change
        omega.1.toEquiv omega.2 (0 : Fin 2) =
          v13RealLinearSwapShear10.toEquiv bridgeX (0 : Fin 2)
      rw [htargetX]
      simp [v13RealLinearSwapShear10, bridgeX]
  have hbranchOmega :
      observer.branch publicBridge = observer.branch publicOmega :=
    observer.branch_eq_of_same_branchRowsTranscript publicOmega publicBridge
      hsameOmega
  have hbridgeRowsZero :
      E.branchRows bridge = ({(0 : Fin 2)} : Finset (Fin 2)) := by
    have hrowsEq :
        observer.rows (observer.branch publicBridge) =
          observer.rows (observer.branch publicOmega) :=
      congrArg observer.rows hbranchOmega
    simpa [E, bridge, publicBridge, v13RealLinearUniformCausalQRowExperiment,
      v13RealLinearUniformQRowExperiment,
      V13RealLinearAdaptiveQRowExperiment.branchRows,
      V13RealLinearAdaptiveQRowExperiment.branch,
      V13RealLinearCausalRowObserver.toAdaptive,
      V13RealLinearCausalRowObserver.staticBranch] using
        hrowsEq.trans homegaObserverRows
  have honeZero :
      ({(1 : Fin 2)} : Finset (Fin 2)) =
        ({(0 : Fin 2)} : Finset (Fin 2)) :=
    hbridgeRowsOne.symm.trans hbridgeRowsZero
  have hmem : (1 : Fin 2) ∈ ({(0 : Fin 2)} : Finset (Fin 2)) := by
    rw [← honeZero]
    simp
  simp at hmem

theorem v13RealLinearShear01_branchRows_ne_empty_of_activeRowIndex_one
    (observer : V13RealLinearCausalRowObserver 2 1) (x : F2Vec 2)
    (activeRow :
      V13RealLinearUniformOneRowGeneratedRowIndex
        observer.toAdaptive (1 : Fin 2)) :
    (v13RealLinearUniformCausalQRowExperiment observer).branchRows
        (v13RealLinearShear01, x) ≠ ∅ := by
  classical
  rcases activeRow.property with ⟨idx, _hidx⟩
  rcases idx.property with
    ⟨omega, _hgen, homegaRows, _htarget, _hbit⟩
  exact
    v13RealLinearShear01_branchRows_ne_empty_of_singletonWitness_one
      observer x omega idx.val.1 homegaRows

theorem v13RealLinearShear01_branchRows_ne_zero_of_activeRowOne_one
    (observer : V13RealLinearCausalRowObserver 2 1) (x : F2Vec 2)
    (activeRow :
      V13RealLinearUniformOneRowGeneratedRowIndex
        observer.toAdaptive (1 : Fin 2))
    (hrow : activeRow.val = (1 : Fin 2)) :
    (v13RealLinearUniformCausalQRowExperiment observer).branchRows
        (v13RealLinearShear01, x) ≠
      ({(0 : Fin 2)} : Finset (Fin 2)) := by
  classical
  rcases activeRow.property with ⟨idx, hidx⟩
  rcases idx.property with
    ⟨omega, _hgen, homegaRows, htarget, _hbit⟩
  have hidxRow : idx.val.1 = (1 : Fin 2) := by
    exact hidx.trans hrow
  have homegaRowsOne :
      (v13RealLinearUniformCausalQRowExperiment observer).branchRows omega =
        ({(1 : Fin 2)} : Finset (Fin 2)) := by
    simpa [v13RealLinearUniformCausalQRowExperiment, hidxRow] using homegaRows
  have htargetOne :
      (1 : Fin 2) ∈ V13RealLinearTargetRows omega.1 (1 : Fin 2) := by
    simpa [hidxRow] using htarget
  exact
    v13RealLinearShear01_branchRows_ne_zero_of_singletonOneWitness_one
      observer x omega homegaRowsOne htargetOne

theorem v13RealLinearShear01_branchRows_ne_one_of_activeRowZero_one
    (observer : V13RealLinearCausalRowObserver 2 1) (x : F2Vec 2)
    (activeRow :
      V13RealLinearUniformOneRowGeneratedRowIndex
        observer.toAdaptive (1 : Fin 2))
    (hrow : activeRow.val = (0 : Fin 2)) :
    (v13RealLinearUniformCausalQRowExperiment observer).branchRows
        (v13RealLinearShear01, x) ≠
      ({(1 : Fin 2)} : Finset (Fin 2)) := by
  classical
  rcases activeRow.property with ⟨idx, hidx⟩
  rcases idx.property with
    ⟨omega, _hgen, homegaRows, htarget, _hbit⟩
  have hidxRow : idx.val.1 = (0 : Fin 2) := by
    exact hidx.trans hrow
  have homegaRowsZero :
      (v13RealLinearUniformCausalQRowExperiment observer).branchRows omega =
        ({(0 : Fin 2)} : Finset (Fin 2)) := by
    simpa [v13RealLinearUniformCausalQRowExperiment, hidxRow] using homegaRows
  have htargetZero :
      (0 : Fin 2) ∈ V13RealLinearTargetRows omega.1 (1 : Fin 2) := by
    simpa [hidxRow] using htarget
  exact
    v13RealLinearShear01_branchRows_ne_one_of_singletonZeroWitness_one
      observer x omega homegaRowsZero htargetZero

theorem v13RealLinearUniformCausalOneRowActiveRowPairExclusion_two_one
    (observer : V13RealLinearCausalRowObserver 2 1)
    (row₀ row₁ :
      V13RealLinearUniformOneRowGeneratedRowIndex
        observer.toAdaptive (1 : Fin 2)) :
    row₀.val = row₁.val := by
  classical
  have hfin : ∀ r : Fin 2, r = (0 : Fin 2) ∨ r = (1 : Fin 2) := by
    intro r
    fin_cases r <;> simp
  rcases hfin row₀.val with hrow₀zero | hrow₀one
  · rcases hfin row₁.val with hrow₁zero | hrow₁one
    · rw [hrow₀zero, hrow₁zero]
    · let x : F2Vec 2 := fun _ => 0
      have hcases := v13RealLinearShear01_branchRows_cases observer x
      rcases hcases with hempty | hrest
      · exact False.elim
          (v13RealLinearShear01_branchRows_ne_empty_of_activeRowIndex_one
            observer x row₀ hempty)
      · rcases hrest with hzero | hone
        · exact False.elim
            (v13RealLinearShear01_branchRows_ne_zero_of_activeRowOne_one
              observer x row₁ hrow₁one hzero)
        · exact False.elim
            (v13RealLinearShear01_branchRows_ne_one_of_activeRowZero_one
              observer x row₀ hrow₀zero hone)
  · rcases hfin row₁.val with hrow₁zero | hrow₁one
    · let x : F2Vec 2 := fun _ => 0
      have hcases := v13RealLinearShear01_branchRows_cases observer x
      rcases hcases with hempty | hrest
      · exact False.elim
          (v13RealLinearShear01_branchRows_ne_empty_of_activeRowIndex_one
            observer x row₀ hempty)
      · rcases hrest with hzero | hone
        · exact False.elim
            (v13RealLinearShear01_branchRows_ne_zero_of_activeRowOne_one
              observer x row₀ hrow₀one hzero)
        · exact False.elim
            (v13RealLinearShear01_branchRows_ne_one_of_activeRowZero_one
              observer x row₁ hrow₁zero hone)
    · rw [hrow₀one, hrow₁one]

noncomputable def
    v13RealLinearUniformOneRowGeneratedCylinderIndexToRowBit
    {m : Nat} (observer : V13RealLinearAdaptiveRowObserver m 1)
    (i₀ : Fin m) :
    V13RealLinearUniformOneRowGeneratedCylinderIndex observer i₀ ↪
      V13RealLinearUniformOneRowGeneratedRowIndex observer i₀ × ZMod 2 where
  toFun idx :=
    (⟨idx.val.1, ⟨idx, rfl⟩⟩, idx.val.2)
  inj' := by
    intro idx₀ idx₁ h
    apply Subtype.ext
    have hrowIndex :
        (⟨idx₀.val.1, ⟨idx₀, rfl⟩⟩ :
            V13RealLinearUniformOneRowGeneratedRowIndex observer i₀) =
          (⟨idx₁.val.1, ⟨idx₁, rfl⟩⟩ :
            V13RealLinearUniformOneRowGeneratedRowIndex observer i₀) :=
      congrArg Prod.fst h
    have hrow : idx₀.val.1 = idx₁.val.1 :=
      congrArg Subtype.val hrowIndex
    have hbit : idx₀.val.2 = idx₁.val.2 := by
      simpa using
        congrArg
          (fun p :
              V13RealLinearUniformOneRowGeneratedRowIndex observer i₀ ×
                ZMod 2 => p.2) h
    exact Prod.ext hrow hbit

theorem v13RealLinearUniformOneRowGeneratedCylinderIndex_card_le_rowIndex_mul_two
    {m : Nat} (observer : V13RealLinearAdaptiveRowObserver m 1)
    (i₀ : Fin m) :
    Fintype.card
        (V13RealLinearUniformOneRowGeneratedCylinderIndex observer i₀) ≤
      Fintype.card
          (V13RealLinearUniformOneRowGeneratedRowIndex observer i₀) * 2 := by
  classical
  have hcard :
      Fintype.card
          (V13RealLinearUniformOneRowGeneratedCylinderIndex observer i₀) ≤
        Fintype.card
          (V13RealLinearUniformOneRowGeneratedRowIndex observer i₀ ×
            ZMod 2) :=
    Fintype.card_le_of_embedding
      (v13RealLinearUniformOneRowGeneratedCylinderIndexToRowBit
        observer i₀)
  simpa [Fintype.card_prod] using hcard

abbrev V13RealLinearUniformOneRowGeneratedCylinderCover
    {m : Nat} (observer : V13RealLinearAdaptiveRowObserver m 1)
    (i₀ : Fin m) :=
  Σ idx : V13RealLinearUniformOneRowGeneratedCylinderIndex observer i₀,
    V13RealLinearUniformFixedTargetRowBitCylinder idx.val.1 i₀ idx.val.2

noncomputable def
    v13RealLinearUniformOneRowGeneratedToActiveBitCylinderCover
    {m : Nat} (observer : V13RealLinearAdaptiveRowObserver m 1)
    (i₀ : Fin m) :
    V13RealLinearAdaptiveQRowGenerated
        (v13RealLinearUniformQRowExperiment observer) i₀ ↪
      V13RealLinearUniformOneRowGeneratedCylinderCover observer i₀ where
  toFun omega := by
    classical
    let E := v13RealLinearUniformQRowExperiment observer
    have htargetExists :=
      E.generated_one_budget_exists_singleton_target_row i₀ omega.val
        omega.property
    let row : Fin m := Classical.choose htargetExists
    have hspec := Classical.choose_spec htargetExists
    have hrows :
        E.branchRows omega.val = ({row} : Finset (Fin m)) := hspec.1
    have htarget :
        row ∈ V13RealLinearTargetRows omega.val.1 i₀ := by
      simpa [E, v13RealLinearUniformQRowExperiment, row] using hspec.2
    let bit : ZMod 2 := omega.val.2 i₀
    refine
      ⟨⟨(row, bit), ?_⟩,
        { A := omega.val.1
          x := omega.val.2
          targetRow := htarget
          targetBit := rfl }⟩
    exact ⟨omega.val, omega.property, hrows, htarget, rfl⟩
  inj' := by
    intro omega₀ omega₁ hmap
    apply Subtype.ext
    apply Prod.ext
    · exact
        congrArg
          (fun data :
              V13RealLinearUniformOneRowGeneratedCylinderCover
                observer i₀ =>
              data.2.A) hmap
    · exact
        congrArg
          (fun data :
              V13RealLinearUniformOneRowGeneratedCylinderCover
                observer i₀ =>
              data.2.x) hmap

theorem v13RealLinearUniformOneRowGenerated_card_le_activeBitCylinderCover
    {m : Nat} (observer : V13RealLinearAdaptiveRowObserver m 1)
    (i₀ : Fin m) :
    Fintype.card
        (V13RealLinearAdaptiveQRowGenerated
          (v13RealLinearUniformQRowExperiment observer) i₀) ≤
      Fintype.card
        (V13RealLinearUniformOneRowGeneratedCylinderCover observer i₀) :=
  Fintype.card_le_of_embedding
    (v13RealLinearUniformOneRowGeneratedToActiveBitCylinderCover
      observer i₀)

theorem v13RealLinearUniformOneRowGenerated_counting_by_activeBitCylinderIndex
    {m : Nat} (observer : V13RealLinearAdaptiveRowObserver m 1)
    (i₀ : Fin m) :
    Fintype.card
        (V13RealLinearAdaptiveQRowGenerated
          (v13RealLinearUniformQRowExperiment observer) i₀) *
        2 ^ m ≤
      Fintype.card
          (V13RealLinearUniformOneRowGeneratedCylinderIndex observer i₀) *
        Fintype.card
          (V13RealLinearAdaptiveQRowWorld m (V13F2LinearEquiv m)) := by
  classical
  let G :=
    Fintype.card
      (V13RealLinearAdaptiveQRowGenerated
        (v13RealLinearUniformQRowExperiment observer) i₀)
  let I :=
    V13RealLinearUniformOneRowGeneratedCylinderIndex observer i₀
  let C := V13RealLinearUniformOneRowGeneratedCylinderCover observer i₀
  let X := 2 ^ m
  let W :=
    Fintype.card
      (V13RealLinearAdaptiveQRowWorld m (V13F2LinearEquiv m))
  have hG : G ≤ Fintype.card C := by
    simpa [G, C] using
      v13RealLinearUniformOneRowGenerated_card_le_activeBitCylinderCover
        observer i₀
  have hC :
      Fintype.card C =
        ∑ idx : I,
          Fintype.card
            (V13RealLinearUniformFixedTargetRowBitCylinder
              idx.val.1 i₀ idx.val.2) := by
    dsimp [C, I, V13RealLinearUniformOneRowGeneratedCylinderCover]
    rw [Fintype.card_sigma]
  calc
    G * X ≤ Fintype.card C * X := Nat.mul_le_mul_right X hG
    _ =
        (∑ idx : I,
          Fintype.card
            (V13RealLinearUniformFixedTargetRowBitCylinder
              idx.val.1 i₀ idx.val.2)) * X := by rw [hC]
    _ =
        ∑ idx : I,
          Fintype.card
              (V13RealLinearUniformFixedTargetRowBitCylinder
                idx.val.1 i₀ idx.val.2) * X := by
      rw [Finset.sum_mul]
    _ ≤ ∑ _idx : I, W := by
      apply Finset.sum_le_sum
      intro idx _hidx
      simpa [X, W] using
        v13RealLinearFixedTargetRowBitCylinder_counting
          idx.val.1 i₀ idx.val.2
    _ = Fintype.card I * W := by
      simp

theorem
    v13RealLinearUniformCausalOneRowGenerated_counting_by_activeBitCylinderIndex
    {m : Nat} (observer : V13RealLinearCausalRowObserver m 1)
    (i₀ : Fin m) :
    Fintype.card
        (V13RealLinearAdaptiveQRowGenerated
          (v13RealLinearUniformCausalQRowExperiment observer) i₀) *
        2 ^ m ≤
      Fintype.card
          (V13RealLinearUniformOneRowGeneratedCylinderIndex
            observer.toAdaptive i₀) *
        Fintype.card
          (V13RealLinearAdaptiveQRowWorld m (V13F2LinearEquiv m)) := by
  change
    Fintype.card
        (V13RealLinearAdaptiveQRowGenerated
          (v13RealLinearUniformQRowExperiment observer.toAdaptive) i₀) *
        2 ^ m ≤
      Fintype.card
          (V13RealLinearUniformOneRowGeneratedCylinderIndex
            observer.toAdaptive i₀) *
        Fintype.card
          (V13RealLinearAdaptiveQRowWorld m (V13F2LinearEquiv m))
  exact
    v13RealLinearUniformOneRowGenerated_counting_by_activeBitCylinderIndex
      observer.toAdaptive i₀

/-- Exact q = 1 sub-obligation left by the active-cylinder reduction: a causal
one-row observer should activate at most the two target-bit cylinders needed
for the `2 / 2^m` bound. -/
def V13RealLinearUniformCausalOneRowActiveBitCylinderIndexBound : Prop :=
  ∀ {m : Nat} (observer : V13RealLinearCausalRowObserver m 1)
    (i₀ : Fin m),
    1 < m →
      Fintype.card
          (V13RealLinearUniformOneRowGeneratedCylinderIndex
            observer.toAdaptive i₀) ≤ 2

/-- Sharper q = 1 row-choice sub-obligation: after forgetting the target bit,
a causal one-row observer should activate at most one generated target row.
Together with the two possible target bits, this implies the active row/bit
cylinder bound. -/
def V13RealLinearUniformCausalOneRowActiveRowIndexBound : Prop :=
  ∀ {m : Nat} (observer : V13RealLinearCausalRowObserver m 1)
    (i₀ : Fin m),
    1 < m →
      Fintype.card
          (V13RealLinearUniformOneRowGeneratedRowIndex
            observer.toAdaptive i₀) ≤ 1

/-- Pairwise form of the active-row q = 1 hard core: any two active generated
target rows for the same causal one-row observer are the same row. -/
def V13RealLinearUniformCausalOneRowActiveRowPairExclusion : Prop :=
  ∀ {m : Nat} (observer : V13RealLinearCausalRowObserver m 1)
    (i₀ : Fin m),
    1 < m →
      ∀ row₀ row₁ :
        V13RealLinearUniformOneRowGeneratedRowIndex
          observer.toAdaptive i₀,
        row₀.val = row₁.val

theorem V13RealLinearUniformCausalOneRowActiveRowIndexBound_of_pairExclusion
    (hpair :
      V13RealLinearUniformCausalOneRowActiveRowPairExclusion) :
    V13RealLinearUniformCausalOneRowActiveRowIndexBound := by
  intro m observer i₀ hm
  rw [Fintype.card_le_one_iff]
  intro row₀ row₁
  apply Subtype.ext
  exact hpair observer i₀ hm row₀ row₁

theorem V13RealLinearUniformCausalOneRowActiveRowPairExclusion_of_indexBound
    (hrow :
      V13RealLinearUniformCausalOneRowActiveRowIndexBound) :
    V13RealLinearUniformCausalOneRowActiveRowPairExclusion := by
  intro m observer i₀ hm row₀ row₁
  have hcard :
      Fintype.card
          (V13RealLinearUniformOneRowGeneratedRowIndex
            observer.toAdaptive i₀) ≤ 1 :=
    hrow observer i₀ hm
  have hsame : row₀ = row₁ := by
    rw [Fintype.card_le_one_iff] at hcard
    exact hcard row₀ row₁
  exact congrArg Subtype.val hsame

theorem V13RealLinearUniformCausalOneRowActiveRowIndexBound_iff_pairExclusion :
    V13RealLinearUniformCausalOneRowActiveRowIndexBound ↔
      V13RealLinearUniformCausalOneRowActiveRowPairExclusion :=
  ⟨V13RealLinearUniformCausalOneRowActiveRowPairExclusion_of_indexBound,
    V13RealLinearUniformCausalOneRowActiveRowIndexBound_of_pairExclusion⟩

theorem
    V13RealLinearUniformCausalOneRowActiveBitCylinderIndexBound_of_rowIndexBound
    (hrow :
      V13RealLinearUniformCausalOneRowActiveRowIndexBound) :
    V13RealLinearUniformCausalOneRowActiveBitCylinderIndexBound := by
  intro m observer i₀ hm
  let R :=
    Fintype.card
      (V13RealLinearUniformOneRowGeneratedRowIndex
        observer.toAdaptive i₀)
  calc
    Fintype.card
        (V13RealLinearUniformOneRowGeneratedCylinderIndex
          observer.toAdaptive i₀) ≤ R * 2 := by
      simpa [R] using
        v13RealLinearUniformOneRowGeneratedCylinderIndex_card_le_rowIndex_mul_two
          observer.toAdaptive i₀
    _ ≤ 1 * 2 := Nat.mul_le_mul_right 2 (by simpa [R] using hrow observer i₀ hm)
    _ = 2 := by norm_num

theorem
    V13RealLinearUniformCausalOneRowActiveRowPairExclusion_of_noTargetRestMismatch
    (hmismatch :
      V13RealLinearUniformCausalOneRowNoTargetRestMismatchExclusion) :
    V13RealLinearUniformCausalOneRowActiveRowPairExclusion := by
  classical
  intro m observer i₀ hm row₀ row₁
  let restX : F2Vec m := fun _ => 0
  obtain ⟨restRow, hrestRows⟩ :=
    v13RealLinearNoTargetRowShear_branchRows_eq_singleton_of_activeRowIndex
      observer i₀ hm restX row₀
  by_cases hrow₀ : row₀.val = restRow
  · by_cases hrow₁ : row₁.val = restRow
    · exact hrow₀.trans hrow₁.symm
    · exact
        False.elim
          (hmismatch observer i₀ hm restX row₁ restRow hrow₁ hrestRows)
  · exact
      False.elim
        (hmismatch observer i₀ hm restX row₀ restRow hrow₀ hrestRows)

theorem
    V13RealLinearUniformCausalOneRowActiveRowIndexBound_of_noTargetRestMismatch
    (hmismatch :
      V13RealLinearUniformCausalOneRowNoTargetRestMismatchExclusion) :
    V13RealLinearUniformCausalOneRowActiveRowIndexBound :=
  V13RealLinearUniformCausalOneRowActiveRowIndexBound_of_pairExclusion
    (V13RealLinearUniformCausalOneRowActiveRowPairExclusion_of_noTargetRestMismatch
      hmismatch)

theorem
    V13RealLinearUniformCausalOneRowActiveBitCylinderIndexBound_of_noTargetRestMismatch
    (hmismatch :
      V13RealLinearUniformCausalOneRowNoTargetRestMismatchExclusion) :
    V13RealLinearUniformCausalOneRowActiveBitCylinderIndexBound :=
  V13RealLinearUniformCausalOneRowActiveBitCylinderIndexBound_of_rowIndexBound
    (V13RealLinearUniformCausalOneRowActiveRowIndexBound_of_noTargetRestMismatch
      hmismatch)

theorem
    v13RealLinearUniformCausalOneRowGenerated_counting_of_activeBitCylinderIndex_le_two
    {m : Nat} (observer : V13RealLinearCausalRowObserver m 1)
    (i₀ : Fin m)
    (hindex :
      Fintype.card
          (V13RealLinearUniformOneRowGeneratedCylinderIndex
            observer.toAdaptive i₀) ≤ 2) :
    Fintype.card
        (V13RealLinearAdaptiveQRowGenerated
          (v13RealLinearUniformCausalQRowExperiment observer) i₀) *
        2 ^ m ≤
      2 ^ 1 *
        Fintype.card
          (V13RealLinearAdaptiveQRowWorld m (V13F2LinearEquiv m)) := by
  classical
  let I :=
    Fintype.card
      (V13RealLinearUniformOneRowGeneratedCylinderIndex
        observer.toAdaptive i₀)
  let W :=
    Fintype.card
      (V13RealLinearAdaptiveQRowWorld m (V13F2LinearEquiv m))
  calc
    Fintype.card
        (V13RealLinearAdaptiveQRowGenerated
          (v13RealLinearUniformCausalQRowExperiment observer) i₀) *
        2 ^ m ≤ I * W := by
      simpa [I, W] using
        v13RealLinearUniformCausalOneRowGenerated_counting_by_activeBitCylinderIndex
          observer i₀
    _ ≤ 2 * W := Nat.mul_le_mul_right W hindex
    _ = 2 ^ 1 * W := by norm_num

theorem
    v13RealLinearUniformCausalOneRowGenerated_counting_of_activeBitCylinderIndexBound
    (hindex :
      V13RealLinearUniformCausalOneRowActiveBitCylinderIndexBound)
    {m : Nat} (observer : V13RealLinearCausalRowObserver m 1)
    (i₀ : Fin m) (hm : 1 < m) :
    Fintype.card
        (V13RealLinearAdaptiveQRowGenerated
          (v13RealLinearUniformCausalQRowExperiment observer) i₀) *
        2 ^ m ≤
      2 ^ 1 *
        Fintype.card
          (V13RealLinearAdaptiveQRowWorld m (V13F2LinearEquiv m)) :=
  v13RealLinearUniformCausalOneRowGenerated_counting_of_activeBitCylinderIndex_le_two
    observer i₀ (hindex observer i₀ hm)

theorem
    v13RealLinearUniformCausalOneRowGenerated_counting_of_activeRowIndexBound
    (hrow :
      V13RealLinearUniformCausalOneRowActiveRowIndexBound)
    {m : Nat} (observer : V13RealLinearCausalRowObserver m 1)
    (i₀ : Fin m) (hm : 1 < m) :
    Fintype.card
        (V13RealLinearAdaptiveQRowGenerated
          (v13RealLinearUniformCausalQRowExperiment observer) i₀) *
        2 ^ m ≤
      2 ^ 1 *
        Fintype.card
          (V13RealLinearAdaptiveQRowWorld m (V13F2LinearEquiv m)) :=
  v13RealLinearUniformCausalOneRowGenerated_counting_of_activeBitCylinderIndexBound
    (V13RealLinearUniformCausalOneRowActiveBitCylinderIndexBound_of_rowIndexBound
      hrow)
    observer i₀ hm

theorem
    v13RealLinearUniformCausalOneRowGenerated_counting_of_activeRowPairExclusion
    (hpair :
      V13RealLinearUniformCausalOneRowActiveRowPairExclusion)
    {m : Nat} (observer : V13RealLinearCausalRowObserver m 1)
    (i₀ : Fin m) (hm : 1 < m) :
    Fintype.card
        (V13RealLinearAdaptiveQRowGenerated
          (v13RealLinearUniformCausalQRowExperiment observer) i₀) *
        2 ^ m ≤
      2 ^ 1 *
        Fintype.card
          (V13RealLinearAdaptiveQRowWorld m (V13F2LinearEquiv m)) :=
  v13RealLinearUniformCausalOneRowGenerated_counting_of_activeRowIndexBound
    (V13RealLinearUniformCausalOneRowActiveRowIndexBound_of_pairExclusion
      hpair)
    observer i₀ hm

theorem
    v13RealLinearUniformCausalOneRowGenerated_counting_of_noTargetRestMismatch
    (hmismatch :
      V13RealLinearUniformCausalOneRowNoTargetRestMismatchExclusion)
    {m : Nat} (observer : V13RealLinearCausalRowObserver m 1)
    (i₀ : Fin m) (hm : 1 < m) :
    Fintype.card
        (V13RealLinearAdaptiveQRowGenerated
          (v13RealLinearUniformCausalQRowExperiment observer) i₀) *
        2 ^ m ≤
      2 ^ 1 *
        Fintype.card
          (V13RealLinearAdaptiveQRowWorld m (V13F2LinearEquiv m)) :=
  v13RealLinearUniformCausalOneRowGenerated_counting_of_activeRowPairExclusion
    (V13RealLinearUniformCausalOneRowActiveRowPairExclusion_of_noTargetRestMismatch
      hmismatch)
    observer i₀ hm

theorem
    v13RealLinearUniformCausalOneRowRowSpanCountingBound_of_activeBitCylinderIndexBound
    (hindex :
      V13RealLinearUniformCausalOneRowActiveBitCylinderIndexBound)
    {m : Nat} (observer : V13RealLinearCausalRowObserver m 1)
    (i₀ : Fin m) (hm : 1 < m) :
    V13RealLinearUniformCausalRowSpanCountingBound observer i₀ :=
  v13RealLinearUniformCausalRowSpanCountingBound_of_generated_counting
    observer i₀
    (v13RealLinearUniformCausalOneRowGenerated_counting_of_activeBitCylinderIndexBound
      hindex observer i₀ hm)

theorem
    v13RealLinearUniformCausalOneRowRowSpanCountingBound_of_activeRowIndexBound
    (hrow :
      V13RealLinearUniformCausalOneRowActiveRowIndexBound)
    {m : Nat} (observer : V13RealLinearCausalRowObserver m 1)
    (i₀ : Fin m) (hm : 1 < m) :
    V13RealLinearUniformCausalRowSpanCountingBound observer i₀ :=
  v13RealLinearUniformCausalOneRowRowSpanCountingBound_of_activeBitCylinderIndexBound
    (V13RealLinearUniformCausalOneRowActiveBitCylinderIndexBound_of_rowIndexBound
      hrow)
    observer i₀ hm

theorem
    v13RealLinearUniformCausalOneRowRowSpanCountingBound_of_activeRowPairExclusion
    (hpair :
      V13RealLinearUniformCausalOneRowActiveRowPairExclusion)
    {m : Nat} (observer : V13RealLinearCausalRowObserver m 1)
    (i₀ : Fin m) (hm : 1 < m) :
    V13RealLinearUniformCausalRowSpanCountingBound observer i₀ :=
  v13RealLinearUniformCausalOneRowRowSpanCountingBound_of_activeRowIndexBound
    (V13RealLinearUniformCausalOneRowActiveRowIndexBound_of_pairExclusion
      hpair)
    observer i₀ hm

theorem
    v13RealLinearUniformCausalOneRowRowSpanCountingBound_of_noTargetRestMismatch
    (hmismatch :
      V13RealLinearUniformCausalOneRowNoTargetRestMismatchExclusion)
    {m : Nat} (observer : V13RealLinearCausalRowObserver m 1)
    (i₀ : Fin m) (hm : 1 < m) :
    V13RealLinearUniformCausalRowSpanCountingBound observer i₀ :=
  v13RealLinearUniformCausalOneRowRowSpanCountingBound_of_activeRowPairExclusion
    (V13RealLinearUniformCausalOneRowActiveRowPairExclusion_of_noTargetRestMismatch
      hmismatch)
    observer i₀ hm

theorem
    v13RealLinear_uniform_causal_one_row_success_bound_of_activeBitCylinderIndexBound
    (hindex :
      V13RealLinearUniformCausalOneRowActiveBitCylinderIndexBound)
    {m : Nat} (observer : V13RealLinearCausalRowObserver m 1)
    (i₀ : Fin m) (hm : 1 < m) :
    v13RealLinearUniformCausalQRowSuccess observer i₀ ≤
      (1 / 2 : Rat) + v13RealLinearQRowEpsilon 1 m :=
  v13RealLinear_uniform_causal_qrow_success_bound_of_spanCounting
    observer i₀
    (v13RealLinearUniformCausalOneRowRowSpanCountingBound_of_activeBitCylinderIndexBound
      hindex observer i₀ hm)

theorem
    v13RealLinear_uniform_causal_one_row_success_bound_of_activeRowIndexBound
    (hrow :
      V13RealLinearUniformCausalOneRowActiveRowIndexBound)
    {m : Nat} (observer : V13RealLinearCausalRowObserver m 1)
    (i₀ : Fin m) (hm : 1 < m) :
    v13RealLinearUniformCausalQRowSuccess observer i₀ ≤
      (1 / 2 : Rat) + v13RealLinearQRowEpsilon 1 m :=
  v13RealLinear_uniform_causal_one_row_success_bound_of_activeBitCylinderIndexBound
    (V13RealLinearUniformCausalOneRowActiveBitCylinderIndexBound_of_rowIndexBound
      hrow)
    observer i₀ hm

theorem
    v13RealLinear_uniform_causal_one_row_success_bound_of_activeRowPairExclusion
    (hpair :
      V13RealLinearUniformCausalOneRowActiveRowPairExclusion)
    {m : Nat} (observer : V13RealLinearCausalRowObserver m 1)
    (i₀ : Fin m) (hm : 1 < m) :
    v13RealLinearUniformCausalQRowSuccess observer i₀ ≤
      (1 / 2 : Rat) + v13RealLinearQRowEpsilon 1 m :=
  v13RealLinear_uniform_causal_one_row_success_bound_of_activeRowIndexBound
    (V13RealLinearUniformCausalOneRowActiveRowIndexBound_of_pairExclusion
      hpair)
    observer i₀ hm

theorem
    v13RealLinear_uniform_causal_one_row_success_bound_of_noTargetRestMismatch
    (hmismatch :
      V13RealLinearUniformCausalOneRowNoTargetRestMismatchExclusion)
    {m : Nat} (observer : V13RealLinearCausalRowObserver m 1)
    (i₀ : Fin m) (hm : 1 < m) :
    v13RealLinearUniformCausalQRowSuccess observer i₀ ≤
      (1 / 2 : Rat) + v13RealLinearQRowEpsilon 1 m :=
  v13RealLinear_uniform_causal_one_row_success_bound_of_activeRowPairExclusion
    (V13RealLinearUniformCausalOneRowActiveRowPairExclusion_of_noTargetRestMismatch
      hmismatch)
    observer i₀ hm

theorem V13RealLinearUniformCausalOneRowActiveRowPairExclusion_proved :
    V13RealLinearUniformCausalOneRowActiveRowPairExclusion :=
  V13RealLinearUniformCausalOneRowActiveRowPairExclusion_of_noTargetRestMismatch
    V13RealLinearUniformCausalOneRowNoTargetRestMismatchExclusion_proved

theorem V13RealLinearUniformCausalOneRowActiveRowIndexBound_proved :
    V13RealLinearUniformCausalOneRowActiveRowIndexBound :=
  V13RealLinearUniformCausalOneRowActiveRowIndexBound_of_noTargetRestMismatch
    V13RealLinearUniformCausalOneRowNoTargetRestMismatchExclusion_proved

theorem V13RealLinearUniformCausalOneRowActiveBitCylinderIndexBound_proved :
    V13RealLinearUniformCausalOneRowActiveBitCylinderIndexBound :=
  V13RealLinearUniformCausalOneRowActiveBitCylinderIndexBound_of_noTargetRestMismatch
    V13RealLinearUniformCausalOneRowNoTargetRestMismatchExclusion_proved

theorem v13RealLinearUniformCausalOneRowGenerated_counting_proved
    {m : Nat} (observer : V13RealLinearCausalRowObserver m 1)
    (i₀ : Fin m) (hm : 1 < m) :
    Fintype.card
        (V13RealLinearAdaptiveQRowGenerated
          (v13RealLinearUniformCausalQRowExperiment observer) i₀) *
        2 ^ m ≤
      2 ^ 1 *
        Fintype.card
          (V13RealLinearAdaptiveQRowWorld m (V13F2LinearEquiv m)) :=
  v13RealLinearUniformCausalOneRowGenerated_counting_of_noTargetRestMismatch
    V13RealLinearUniformCausalOneRowNoTargetRestMismatchExclusion_proved
    observer i₀ hm

theorem v13RealLinearUniformCausalOneRowRowSpanCountingBound_proved
    {m : Nat} (observer : V13RealLinearCausalRowObserver m 1)
    (i₀ : Fin m) (hm : 1 < m) :
    V13RealLinearUniformCausalRowSpanCountingBound observer i₀ :=
  v13RealLinearUniformCausalOneRowRowSpanCountingBound_of_noTargetRestMismatch
    V13RealLinearUniformCausalOneRowNoTargetRestMismatchExclusion_proved
    observer i₀ hm

theorem v13RealLinear_uniform_causal_one_row_success_bound
    {m : Nat} (observer : V13RealLinearCausalRowObserver m 1)
    (i₀ : Fin m) (hm : 1 < m) :
    v13RealLinearUniformCausalQRowSuccess observer i₀ ≤
      (1 / 2 : Rat) + v13RealLinearQRowEpsilon 1 m :=
  v13RealLinear_uniform_causal_one_row_success_bound_of_noTargetRestMismatch
    V13RealLinearUniformCausalOneRowNoTargetRestMismatchExclusion_proved
    observer i₀ hm

theorem
    v13RealLinearUniformCausalOneRowActiveRowIndexBound_two_zero
    (observer : V13RealLinearCausalRowObserver 2 1) :
    Fintype.card
        (V13RealLinearUniformOneRowGeneratedRowIndex
          observer.toAdaptive (0 : Fin 2)) ≤ 1 := by
  classical
  rw [Fintype.card_le_one_iff]
  intro row₀ row₁
  apply Subtype.ext
  exact
    v13RealLinearUniformCausalOneRowActiveRowPairExclusion_two_zero
      observer row₀ row₁

theorem
    v13RealLinearUniformCausalOneRowActiveBitCylinderIndexBound_two_zero
    (observer : V13RealLinearCausalRowObserver 2 1) :
    Fintype.card
        (V13RealLinearUniformOneRowGeneratedCylinderIndex
          observer.toAdaptive (0 : Fin 2)) ≤ 2 := by
  let R :=
    Fintype.card
      (V13RealLinearUniformOneRowGeneratedRowIndex
        observer.toAdaptive (0 : Fin 2))
  calc
    Fintype.card
        (V13RealLinearUniformOneRowGeneratedCylinderIndex
          observer.toAdaptive (0 : Fin 2)) ≤ R * 2 := by
      simpa [R] using
        v13RealLinearUniformOneRowGeneratedCylinderIndex_card_le_rowIndex_mul_two
          observer.toAdaptive (0 : Fin 2)
    _ ≤ 1 * 2 := Nat.mul_le_mul_right 2 (by
      simpa [R] using
        v13RealLinearUniformCausalOneRowActiveRowIndexBound_two_zero observer)
    _ = 2 := by norm_num

theorem
    v13RealLinearUniformCausalOneRowGenerated_counting_two_zero
    (observer : V13RealLinearCausalRowObserver 2 1) :
    Fintype.card
        (V13RealLinearAdaptiveQRowGenerated
          (v13RealLinearUniformCausalQRowExperiment observer) (0 : Fin 2)) *
        2 ^ 2 ≤
      2 ^ 1 *
        Fintype.card
          (V13RealLinearAdaptiveQRowWorld 2 (V13F2LinearEquiv 2)) :=
  v13RealLinearUniformCausalOneRowGenerated_counting_of_activeBitCylinderIndex_le_two
    observer (0 : Fin 2)
    (v13RealLinearUniformCausalOneRowActiveBitCylinderIndexBound_two_zero
      observer)

theorem v13RealLinearUniformCausalRowSpanCountingBound_one_two_zero
    (observer : V13RealLinearCausalRowObserver 2 1) :
    V13RealLinearUniformCausalRowSpanCountingBound observer (0 : Fin 2) :=
  v13RealLinearUniformCausalRowSpanCountingBound_of_generated_counting
    observer (0 : Fin 2)
    (v13RealLinearUniformCausalOneRowGenerated_counting_two_zero observer)

theorem v13RealLinear_uniform_causal_qrow_success_bound_one_two_zero
    (observer : V13RealLinearCausalRowObserver 2 1) :
    v13RealLinearUniformCausalQRowSuccess observer (0 : Fin 2) ≤
      (1 / 2 : Rat) + v13RealLinearQRowEpsilon 1 2 :=
  v13RealLinear_uniform_causal_qrow_success_bound_of_spanCounting
    observer (0 : Fin 2)
    (v13RealLinearUniformCausalRowSpanCountingBound_one_two_zero observer)

theorem
    v13RealLinearUniformCausalOneRowActiveRowIndexBound_two_one
    (observer : V13RealLinearCausalRowObserver 2 1) :
    Fintype.card
        (V13RealLinearUniformOneRowGeneratedRowIndex
          observer.toAdaptive (1 : Fin 2)) ≤ 1 := by
  classical
  rw [Fintype.card_le_one_iff]
  intro row₀ row₁
  apply Subtype.ext
  exact
    v13RealLinearUniformCausalOneRowActiveRowPairExclusion_two_one
      observer row₀ row₁

theorem
    v13RealLinearUniformCausalOneRowActiveBitCylinderIndexBound_two_one
    (observer : V13RealLinearCausalRowObserver 2 1) :
    Fintype.card
        (V13RealLinearUniformOneRowGeneratedCylinderIndex
          observer.toAdaptive (1 : Fin 2)) ≤ 2 := by
  let R :=
    Fintype.card
      (V13RealLinearUniformOneRowGeneratedRowIndex
        observer.toAdaptive (1 : Fin 2))
  calc
    Fintype.card
        (V13RealLinearUniformOneRowGeneratedCylinderIndex
          observer.toAdaptive (1 : Fin 2)) ≤ R * 2 := by
      simpa [R] using
        v13RealLinearUniformOneRowGeneratedCylinderIndex_card_le_rowIndex_mul_two
          observer.toAdaptive (1 : Fin 2)
    _ ≤ 1 * 2 := Nat.mul_le_mul_right 2 (by
      simpa [R] using
        v13RealLinearUniformCausalOneRowActiveRowIndexBound_two_one observer)
    _ = 2 := by norm_num

theorem
    v13RealLinearUniformCausalOneRowGenerated_counting_two_one
    (observer : V13RealLinearCausalRowObserver 2 1) :
    Fintype.card
        (V13RealLinearAdaptiveQRowGenerated
          (v13RealLinearUniformCausalQRowExperiment observer) (1 : Fin 2)) *
        2 ^ 2 ≤
      2 ^ 1 *
        Fintype.card
          (V13RealLinearAdaptiveQRowWorld 2 (V13F2LinearEquiv 2)) :=
  v13RealLinearUniformCausalOneRowGenerated_counting_of_activeBitCylinderIndex_le_two
    observer (1 : Fin 2)
    (v13RealLinearUniformCausalOneRowActiveBitCylinderIndexBound_two_one
      observer)

theorem v13RealLinearUniformCausalRowSpanCountingBound_one_two_one
    (observer : V13RealLinearCausalRowObserver 2 1) :
    V13RealLinearUniformCausalRowSpanCountingBound observer (1 : Fin 2) :=
  v13RealLinearUniformCausalRowSpanCountingBound_of_generated_counting
    observer (1 : Fin 2)
    (v13RealLinearUniformCausalOneRowGenerated_counting_two_one observer)

theorem v13RealLinear_uniform_causal_qrow_success_bound_one_two_one
    (observer : V13RealLinearCausalRowObserver 2 1) :
    v13RealLinearUniformCausalQRowSuccess observer (1 : Fin 2) ≤
      (1 / 2 : Rat) + v13RealLinearQRowEpsilon 1 2 :=
  v13RealLinear_uniform_causal_qrow_success_bound_of_spanCounting
    observer (1 : Fin 2)
    (v13RealLinearUniformCausalRowSpanCountingBound_one_two_one observer)

theorem v13RealLinearUniformCausalOneRowActiveRowPairExclusion_two
    (observer : V13RealLinearCausalRowObserver 2 1) (i₀ : Fin 2)
    (row₀ row₁ :
      V13RealLinearUniformOneRowGeneratedRowIndex
        observer.toAdaptive i₀) :
    row₀.val = row₁.val := by
  fin_cases i₀
  · exact
      v13RealLinearUniformCausalOneRowActiveRowPairExclusion_two_zero
        observer row₀ row₁
  · exact
      v13RealLinearUniformCausalOneRowActiveRowPairExclusion_two_one
        observer row₀ row₁

theorem
    v13RealLinearUniformCausalOneRowActiveRowIndexBound_one_two
    (observer : V13RealLinearCausalRowObserver 2 1) (i₀ : Fin 2) :
    Fintype.card
        (V13RealLinearUniformOneRowGeneratedRowIndex
          observer.toAdaptive i₀) ≤ 1 := by
  fin_cases i₀
  · exact
      v13RealLinearUniformCausalOneRowActiveRowIndexBound_two_zero observer
  · exact
      v13RealLinearUniformCausalOneRowActiveRowIndexBound_two_one observer

theorem
    v13RealLinearUniformCausalOneRowActiveBitCylinderIndexBound_one_two
    (observer : V13RealLinearCausalRowObserver 2 1) (i₀ : Fin 2) :
    Fintype.card
        (V13RealLinearUniformOneRowGeneratedCylinderIndex
          observer.toAdaptive i₀) ≤ 2 := by
  fin_cases i₀
  · exact
      v13RealLinearUniformCausalOneRowActiveBitCylinderIndexBound_two_zero
        observer
  · exact
      v13RealLinearUniformCausalOneRowActiveBitCylinderIndexBound_two_one
        observer

theorem
    v13RealLinearUniformCausalOneRowGenerated_counting_one_two
    (observer : V13RealLinearCausalRowObserver 2 1) (i₀ : Fin 2) :
    Fintype.card
        (V13RealLinearAdaptiveQRowGenerated
          (v13RealLinearUniformCausalQRowExperiment observer) i₀) *
        2 ^ 2 ≤
      2 ^ 1 *
        Fintype.card
          (V13RealLinearAdaptiveQRowWorld 2 (V13F2LinearEquiv 2)) := by
  fin_cases i₀
  · exact v13RealLinearUniformCausalOneRowGenerated_counting_two_zero observer
  · exact v13RealLinearUniformCausalOneRowGenerated_counting_two_one observer

theorem v13RealLinearUniformCausalRowSpanCountingBound_one_two
    (observer : V13RealLinearCausalRowObserver 2 1) (i₀ : Fin 2) :
    V13RealLinearUniformCausalRowSpanCountingBound observer i₀ := by
  fin_cases i₀
  · exact
      v13RealLinearUniformCausalRowSpanCountingBound_one_two_zero observer
  · exact
      v13RealLinearUniformCausalRowSpanCountingBound_one_two_one observer

theorem v13RealLinear_uniform_causal_qrow_success_bound_one_two
    (observer : V13RealLinearCausalRowObserver 2 1) (i₀ : Fin 2) :
    v13RealLinearUniformCausalQRowSuccess observer i₀ ≤
      (1 / 2 : Rat) + v13RealLinearQRowEpsilon 1 2 := by
  fin_cases i₀
  · exact
      v13RealLinear_uniform_causal_qrow_success_bound_one_two_zero observer
  · exact
      v13RealLinear_uniform_causal_qrow_success_bound_one_two_one observer

noncomputable def v13RealLinearFixedTargetRowOccurrenceZeroEmbedding :
    V13RealLinearUniformFixedTargetRowOccurrence
        (0 : Fin 2) (0 : Fin 2) ↪
      {v : V13RealLinearNonzeroF2Vec2 //
        v.val ≠ v13RealLinearSingleBit (1 : Fin 2)} where
  toFun A := by
    refine ⟨(v13RealLinearTwoBasisImagePair A.val).1, ?_⟩
    have htarget :
        ∀ w : F2Vec 2, A.val.toEquiv w (0 : Fin 2) = w (0 : Fin 2) :=
      (v13RealLinear_mem_targetRows_iff A.val (0 : Fin 2) (0 : Fin 2)).1
        A.property
    have hcoord :
        A.val.toEquiv (v13RealLinearSingleBit (0 : Fin 2)) (0 : Fin 2) = 1 := by
      simpa [v13RealLinearSingleBit] using
        htarget (v13RealLinearSingleBit (0 : Fin 2))
    intro heq
    have hcoordEq := congrFun heq (0 : Fin 2)
    simp [v13RealLinearSingleBit] at hcoordEq
    have hcoordEq' :
        A.val.toEquiv (v13RealLinearSingleBit (0 : Fin 2)) (0 : Fin 2) = 0 := by
      change
        (v13RealLinearTwoBasisImagePair A.val).1.val (0 : Fin 2) = 0
      exact hcoordEq
    rw [hcoordEq'] at hcoord
    norm_num at hcoord
  inj' := by
    intro A B hmap
    apply Subtype.ext
    apply v13RealLinear_equiv_two_ext A.val B.val
    · exact congrArg (fun p =>
        (p.val : V13RealLinearNonzeroF2Vec2).val) hmap
    · have hA :
          A.val.toEquiv (v13RealLinearSingleBit (1 : Fin 2)) =
            v13RealLinearSingleBit (1 : Fin 2) := by
        have htarget :
            ∀ w : F2Vec 2, A.val.toEquiv w (0 : Fin 2) = w (0 : Fin 2) :=
          (v13RealLinear_mem_targetRows_iff
            A.val (0 : Fin 2) (0 : Fin 2)).1 A.property
        have hcoord :
            A.val.toEquiv (v13RealLinearSingleBit (1 : Fin 2))
              (0 : Fin 2) = 0 := by
          simpa [v13RealLinearSingleBit] using
            htarget (v13RealLinearSingleBit (1 : Fin 2))
        exact
          v13RealLinear_f2vec2_eq_singleBit_one_of_ne_zero_of_coord_zero
            (A.val.toEquiv (v13RealLinearSingleBit (1 : Fin 2)))
            (v13RealLinearTwoBasisImagePair A.val).2.val.property hcoord
      have hB :
          B.val.toEquiv (v13RealLinearSingleBit (1 : Fin 2)) =
            v13RealLinearSingleBit (1 : Fin 2) := by
        have htarget :
            ∀ w : F2Vec 2, B.val.toEquiv w (0 : Fin 2) = w (0 : Fin 2) :=
          (v13RealLinear_mem_targetRows_iff
            B.val (0 : Fin 2) (0 : Fin 2)).1 B.property
        have hcoord :
            B.val.toEquiv (v13RealLinearSingleBit (1 : Fin 2))
              (0 : Fin 2) = 0 := by
          simpa [v13RealLinearSingleBit] using
            htarget (v13RealLinearSingleBit (1 : Fin 2))
        exact
          v13RealLinear_f2vec2_eq_singleBit_one_of_ne_zero_of_coord_zero
            (B.val.toEquiv (v13RealLinearSingleBit (1 : Fin 2)))
            (v13RealLinearTwoBasisImagePair B.val).2.val.property hcoord
      exact hA.trans hB.symm

theorem v13RealLinearFixedTargetRowOccurrence_zero_card_le_two :
    Fintype.card
        (V13RealLinearUniformFixedTargetRowOccurrence
          (0 : Fin 2) (0 : Fin 2)) ≤ 2 := by
  classical
  have hone :
      v13RealLinearSingleBit (1 : Fin 2) ≠ f2ZeroVec 2 := by
    intro h
    have hcoord := congrFun h (1 : Fin 2)
    simp [v13RealLinearSingleBit, f2ZeroVec] at hcoord
  have hle :
      Fintype.card
          (V13RealLinearUniformFixedTargetRowOccurrence
            (0 : Fin 2) (0 : Fin 2)) ≤
        Fintype.card
          {v : V13RealLinearNonzeroF2Vec2 //
            v.val ≠ v13RealLinearSingleBit (1 : Fin 2)} :=
    Fintype.card_le_of_embedding
      v13RealLinearFixedTargetRowOccurrenceZeroEmbedding
  exact hle.trans
    (v13RealLinearNonzeroF2Vec2_ne_card_le_two
      ⟨v13RealLinearSingleBit (1 : Fin 2), hone⟩)

noncomputable def v13RealLinearFixedTargetRowOccurrenceOneOneEmbedding :
    V13RealLinearUniformFixedTargetRowOccurrence
        (1 : Fin 2) (1 : Fin 2) ↪
      {v : V13RealLinearNonzeroF2Vec2 //
        v.val ≠ v13RealLinearSingleBit (0 : Fin 2)} where
  toFun A := by
    refine ⟨(v13RealLinearTwoBasisImagePair A.val).2.val, ?_⟩
    have htarget :
        ∀ w : F2Vec 2, A.val.toEquiv w (1 : Fin 2) = w (1 : Fin 2) :=
      (v13RealLinear_mem_targetRows_iff A.val (1 : Fin 2) (1 : Fin 2)).1
        A.property
    have hcoord :
        A.val.toEquiv (v13RealLinearSingleBit (1 : Fin 2)) (1 : Fin 2) = 1 := by
      simpa [v13RealLinearSingleBit] using
        htarget (v13RealLinearSingleBit (1 : Fin 2))
    intro heq
    have hcoordEq := congrFun heq (1 : Fin 2)
    simp [v13RealLinearSingleBit] at hcoordEq
    have hcoordEq' :
        A.val.toEquiv (v13RealLinearSingleBit (1 : Fin 2)) (1 : Fin 2) = 0 := by
      change
        (v13RealLinearTwoBasisImagePair A.val).2.val.val (1 : Fin 2) = 0
      exact hcoordEq
    rw [hcoordEq'] at hcoord
    norm_num at hcoord
  inj' := by
    intro A B hmap
    apply Subtype.ext
    apply v13RealLinear_equiv_two_ext A.val B.val
    · have hA :
          A.val.toEquiv (v13RealLinearSingleBit (0 : Fin 2)) =
            v13RealLinearSingleBit (0 : Fin 2) := by
        have htarget :
            ∀ w : F2Vec 2, A.val.toEquiv w (1 : Fin 2) = w (1 : Fin 2) :=
          (v13RealLinear_mem_targetRows_iff
            A.val (1 : Fin 2) (1 : Fin 2)).1 A.property
        have hcoord :
            A.val.toEquiv (v13RealLinearSingleBit (0 : Fin 2))
              (1 : Fin 2) = 0 := by
          simpa [v13RealLinearSingleBit] using
            htarget (v13RealLinearSingleBit (0 : Fin 2))
        exact
          v13RealLinear_f2vec2_eq_singleBit_zero_of_ne_zero_of_coord_one_zero
            (A.val.toEquiv (v13RealLinearSingleBit (0 : Fin 2)))
            (v13RealLinearTwoBasisImagePair A.val).1.property hcoord
      have hB :
          B.val.toEquiv (v13RealLinearSingleBit (0 : Fin 2)) =
            v13RealLinearSingleBit (0 : Fin 2) := by
        have htarget :
            ∀ w : F2Vec 2, B.val.toEquiv w (1 : Fin 2) = w (1 : Fin 2) :=
          (v13RealLinear_mem_targetRows_iff
            B.val (1 : Fin 2) (1 : Fin 2)).1 B.property
        have hcoord :
            B.val.toEquiv (v13RealLinearSingleBit (0 : Fin 2))
              (1 : Fin 2) = 0 := by
          simpa [v13RealLinearSingleBit] using
            htarget (v13RealLinearSingleBit (0 : Fin 2))
        exact
          v13RealLinear_f2vec2_eq_singleBit_zero_of_ne_zero_of_coord_one_zero
            (B.val.toEquiv (v13RealLinearSingleBit (0 : Fin 2)))
            (v13RealLinearTwoBasisImagePair B.val).1.property hcoord
      exact hA.trans hB.symm
    · exact congrArg (fun p =>
        (p.val : V13RealLinearNonzeroF2Vec2).val) hmap

theorem v13RealLinearFixedTargetRowOccurrence_one_one_card_le_two :
    Fintype.card
        (V13RealLinearUniformFixedTargetRowOccurrence
          (1 : Fin 2) (1 : Fin 2)) ≤ 2 := by
  classical
  have hone :
      v13RealLinearSingleBit (0 : Fin 2) ≠ f2ZeroVec 2 := by
    intro h
    have hcoord := congrFun h (0 : Fin 2)
    simp [v13RealLinearSingleBit, f2ZeroVec] at hcoord
  have hle :
      Fintype.card
          (V13RealLinearUniformFixedTargetRowOccurrence
            (1 : Fin 2) (1 : Fin 2)) ≤
        Fintype.card
          {v : V13RealLinearNonzeroF2Vec2 //
            v.val ≠ v13RealLinearSingleBit (0 : Fin 2)} :=
    Fintype.card_le_of_embedding
      v13RealLinearFixedTargetRowOccurrenceOneOneEmbedding
  exact hle.trans
    (v13RealLinearNonzeroF2Vec2_ne_card_le_two
      ⟨v13RealLinearSingleBit (0 : Fin 2), hone⟩)

noncomputable def v13RealLinearFixedTargetRowOccurrenceZeroOneEmbedding :
    V13RealLinearUniformFixedTargetRowOccurrence
        (0 : Fin 2) (1 : Fin 2) ↪
      {v : V13RealLinearNonzeroF2Vec2 //
        v.val ≠ v13RealLinearSingleBit (1 : Fin 2)} where
  toFun A := by
    refine ⟨(v13RealLinearTwoBasisImagePair A.val).2.val, ?_⟩
    have htarget :
        ∀ w : F2Vec 2, A.val.toEquiv w (0 : Fin 2) = w (1 : Fin 2) :=
      (v13RealLinear_mem_targetRows_iff A.val (1 : Fin 2) (0 : Fin 2)).1
        A.property
    have hcoord :
        A.val.toEquiv (v13RealLinearSingleBit (1 : Fin 2)) (0 : Fin 2) = 1 := by
      simpa [v13RealLinearSingleBit] using
        htarget (v13RealLinearSingleBit (1 : Fin 2))
    intro heq
    have hcoordEq := congrFun heq (0 : Fin 2)
    simp [v13RealLinearSingleBit] at hcoordEq
    have hcoordEq' :
        A.val.toEquiv (v13RealLinearSingleBit (1 : Fin 2)) (0 : Fin 2) = 0 := by
      change
        (v13RealLinearTwoBasisImagePair A.val).2.val.val (0 : Fin 2) = 0
      exact hcoordEq
    rw [hcoordEq'] at hcoord
    norm_num at hcoord
  inj' := by
    intro A B hmap
    apply Subtype.ext
    apply v13RealLinear_equiv_two_ext A.val B.val
    · have hA :
          A.val.toEquiv (v13RealLinearSingleBit (0 : Fin 2)) =
            v13RealLinearSingleBit (1 : Fin 2) := by
        have htarget :
            ∀ w : F2Vec 2, A.val.toEquiv w (0 : Fin 2) = w (1 : Fin 2) :=
          (v13RealLinear_mem_targetRows_iff
            A.val (1 : Fin 2) (0 : Fin 2)).1 A.property
        have hcoord :
            A.val.toEquiv (v13RealLinearSingleBit (0 : Fin 2))
              (0 : Fin 2) = 0 := by
          simpa [v13RealLinearSingleBit] using
            htarget (v13RealLinearSingleBit (0 : Fin 2))
        exact
          v13RealLinear_f2vec2_eq_singleBit_one_of_ne_zero_of_coord_zero
            (A.val.toEquiv (v13RealLinearSingleBit (0 : Fin 2)))
            (v13RealLinearTwoBasisImagePair A.val).1.property hcoord
      have hB :
          B.val.toEquiv (v13RealLinearSingleBit (0 : Fin 2)) =
            v13RealLinearSingleBit (1 : Fin 2) := by
        have htarget :
            ∀ w : F2Vec 2, B.val.toEquiv w (0 : Fin 2) = w (1 : Fin 2) :=
          (v13RealLinear_mem_targetRows_iff
            B.val (1 : Fin 2) (0 : Fin 2)).1 B.property
        have hcoord :
            B.val.toEquiv (v13RealLinearSingleBit (0 : Fin 2))
              (0 : Fin 2) = 0 := by
          simpa [v13RealLinearSingleBit] using
            htarget (v13RealLinearSingleBit (0 : Fin 2))
        exact
          v13RealLinear_f2vec2_eq_singleBit_one_of_ne_zero_of_coord_zero
            (B.val.toEquiv (v13RealLinearSingleBit (0 : Fin 2)))
            (v13RealLinearTwoBasisImagePair B.val).1.property hcoord
      exact hA.trans hB.symm
    · exact congrArg (fun p =>
        (p.val : V13RealLinearNonzeroF2Vec2).val) hmap

theorem v13RealLinearFixedTargetRowOccurrence_zero_one_card_le_two :
    Fintype.card
        (V13RealLinearUniformFixedTargetRowOccurrence
          (0 : Fin 2) (1 : Fin 2)) ≤ 2 := by
  classical
  have hone :
      v13RealLinearSingleBit (1 : Fin 2) ≠ f2ZeroVec 2 := by
    intro h
    have hcoord := congrFun h (1 : Fin 2)
    simp [v13RealLinearSingleBit, f2ZeroVec] at hcoord
  have hle :
      Fintype.card
          (V13RealLinearUniformFixedTargetRowOccurrence
            (0 : Fin 2) (1 : Fin 2)) ≤
        Fintype.card
          {v : V13RealLinearNonzeroF2Vec2 //
            v.val ≠ v13RealLinearSingleBit (1 : Fin 2)} :=
    Fintype.card_le_of_embedding
      v13RealLinearFixedTargetRowOccurrenceZeroOneEmbedding
  exact hle.trans
    (v13RealLinearNonzeroF2Vec2_ne_card_le_two
      ⟨v13RealLinearSingleBit (1 : Fin 2), hone⟩)

noncomputable def v13RealLinearFixedTargetRowOccurrenceOneZeroEmbedding :
    V13RealLinearUniformFixedTargetRowOccurrence
        (1 : Fin 2) (0 : Fin 2) ↪
      {v : V13RealLinearNonzeroF2Vec2 //
        v.val ≠ v13RealLinearSingleBit (0 : Fin 2)} where
  toFun A := by
    refine ⟨(v13RealLinearTwoBasisImagePair A.val).1, ?_⟩
    have htarget :
        ∀ w : F2Vec 2, A.val.toEquiv w (1 : Fin 2) = w (0 : Fin 2) :=
      (v13RealLinear_mem_targetRows_iff A.val (0 : Fin 2) (1 : Fin 2)).1
        A.property
    have hcoord :
        A.val.toEquiv (v13RealLinearSingleBit (0 : Fin 2)) (1 : Fin 2) = 1 := by
      simpa [v13RealLinearSingleBit] using
        htarget (v13RealLinearSingleBit (0 : Fin 2))
    intro heq
    have hcoordEq := congrFun heq (1 : Fin 2)
    simp [v13RealLinearSingleBit] at hcoordEq
    have hcoordEq' :
        A.val.toEquiv (v13RealLinearSingleBit (0 : Fin 2)) (1 : Fin 2) = 0 := by
      change
        (v13RealLinearTwoBasisImagePair A.val).1.val (1 : Fin 2) = 0
      exact hcoordEq
    rw [hcoordEq'] at hcoord
    norm_num at hcoord
  inj' := by
    intro A B hmap
    apply Subtype.ext
    apply v13RealLinear_equiv_two_ext A.val B.val
    · exact congrArg (fun p =>
        (p.val : V13RealLinearNonzeroF2Vec2).val) hmap
    · have hA :
          A.val.toEquiv (v13RealLinearSingleBit (1 : Fin 2)) =
            v13RealLinearSingleBit (0 : Fin 2) := by
        have htarget :
            ∀ w : F2Vec 2, A.val.toEquiv w (1 : Fin 2) = w (0 : Fin 2) :=
          (v13RealLinear_mem_targetRows_iff
            A.val (0 : Fin 2) (1 : Fin 2)).1 A.property
        have hcoord :
            A.val.toEquiv (v13RealLinearSingleBit (1 : Fin 2))
              (1 : Fin 2) = 0 := by
          simpa [v13RealLinearSingleBit] using
            htarget (v13RealLinearSingleBit (1 : Fin 2))
        exact
          v13RealLinear_f2vec2_eq_singleBit_zero_of_ne_zero_of_coord_one_zero
            (A.val.toEquiv (v13RealLinearSingleBit (1 : Fin 2)))
            (v13RealLinearTwoBasisImagePair A.val).2.val.property hcoord
      have hB :
          B.val.toEquiv (v13RealLinearSingleBit (1 : Fin 2)) =
            v13RealLinearSingleBit (0 : Fin 2) := by
        have htarget :
            ∀ w : F2Vec 2, B.val.toEquiv w (1 : Fin 2) = w (0 : Fin 2) :=
          (v13RealLinear_mem_targetRows_iff
            B.val (0 : Fin 2) (1 : Fin 2)).1 B.property
        have hcoord :
            B.val.toEquiv (v13RealLinearSingleBit (1 : Fin 2))
              (1 : Fin 2) = 0 := by
          simpa [v13RealLinearSingleBit] using
            htarget (v13RealLinearSingleBit (1 : Fin 2))
        exact
          v13RealLinear_f2vec2_eq_singleBit_zero_of_ne_zero_of_coord_one_zero
            (B.val.toEquiv (v13RealLinearSingleBit (1 : Fin 2)))
            (v13RealLinearTwoBasisImagePair B.val).2.val.property hcoord
      exact hA.trans hB.symm

theorem v13RealLinearFixedTargetRowOccurrence_one_zero_card_le_two :
    Fintype.card
        (V13RealLinearUniformFixedTargetRowOccurrence
          (1 : Fin 2) (0 : Fin 2)) ≤ 2 := by
  classical
  have hone :
      v13RealLinearSingleBit (0 : Fin 2) ≠ f2ZeroVec 2 := by
    intro h
    have hcoord := congrFun h (0 : Fin 2)
    simp [v13RealLinearSingleBit, f2ZeroVec] at hcoord
  have hle :
      Fintype.card
          (V13RealLinearUniformFixedTargetRowOccurrence
            (1 : Fin 2) (0 : Fin 2)) ≤
        Fintype.card
          {v : V13RealLinearNonzeroF2Vec2 //
            v.val ≠ v13RealLinearSingleBit (0 : Fin 2)} :=
    Fintype.card_le_of_embedding
      v13RealLinearFixedTargetRowOccurrenceOneZeroEmbedding
  exact hle.trans
    (v13RealLinearNonzeroF2Vec2_ne_card_le_two
      ⟨v13RealLinearSingleBit (0 : Fin 2), hone⟩)

theorem v13RealLinearFixedTargetRowOccurrence_two_card_le_two
    (row i₀ : Fin 2) :
    Fintype.card
        (V13RealLinearUniformFixedTargetRowOccurrence row i₀) ≤ 2 := by
  fin_cases row <;> fin_cases i₀
  · exact v13RealLinearFixedTargetRowOccurrence_zero_card_le_two
  · exact v13RealLinearFixedTargetRowOccurrence_zero_one_card_le_two
  · exact v13RealLinearFixedTargetRowOccurrence_one_zero_card_le_two
  · exact v13RealLinearFixedTargetRowOccurrence_one_one_card_le_two

noncomputable def
    v13RealLinear_causalSingleRowGeneratedCoefficientEquivFixedOccurrenceProd
    {m : Nat} (row i₀ : Fin m) :
    V13RealLinearAdaptiveQRowGeneratedCoefficient
        (v13RealLinearUniformCausalQRowExperiment
          (v13RealLinearCausalSingleRowObserver row)) i₀ ≃
      V13RealLinearUniformFixedTargetRowOccurrence row i₀ × F2Vec m where
  toFun cert := by
    refine ⟨⟨cert.val.1.1, ?_⟩, cert.val.1.2⟩
    have hgen :
        V13RealLinearRowsGenerateTarget cert.val.1.1
          ({row} : Finset (Fin m)) i₀ := by
      refine ⟨cert.val.2, ?_⟩
      intro w
      simpa [v13RealLinearUniformCausalQRowExperiment,
        v13RealLinearUniformQRowExperiment,
        V13RealLinearAdaptiveQRowExperiment.branchRows,
        V13RealLinearAdaptiveQRowExperiment.branch,
        V13RealLinearCausalRowObserver.toAdaptive,
        V13RealLinearCausalRowObserver.staticBranch,
        v13RealLinearCausalSingleRowObserver] using cert.property w
    exact
      (v13RealLinear_mem_targetRows_iff cert.val.1.1 i₀ row).2
        ((v13RealLinear_rowsGenerateTarget_singleton_iff
          cert.val.1.1 row i₀).1 hgen)
  invFun pair := by
    refine ⟨⟨(pair.1.val, pair.2), fun _ => 1⟩, ?_⟩
    intro w
    have htarget :
        pair.1.val.toEquiv w row = w i₀ :=
      (v13RealLinear_mem_targetRows_iff pair.1.val i₀ row).1
        pair.1.property w
    simp [v13RealLinearUniformCausalQRowExperiment,
      v13RealLinearUniformQRowExperiment,
      V13RealLinearAdaptiveQRowExperiment.branchRows,
      V13RealLinearAdaptiveQRowExperiment.branch,
      V13RealLinearCausalRowObserver.toAdaptive,
      V13RealLinearCausalRowObserver.staticBranch,
      v13RealLinearCausalSingleRowObserver,
      v13RealLinearRowCombinationEval, htarget]
  left_inv cert := by
    apply Subtype.ext
    apply Sigma.ext
    · rfl
    · simp
      have hcoeff :
          cert.val.2 = fun _ => 1 := by
        apply
          v13RealLinear_singletonRowCombination_eq_one_of_generates
            cert.val.1.1 row i₀ cert.val.2
        intro w
        simpa [v13RealLinearUniformCausalQRowExperiment,
          v13RealLinearUniformQRowExperiment,
          V13RealLinearAdaptiveQRowExperiment.branchRows,
          V13RealLinearAdaptiveQRowExperiment.branch,
          V13RealLinearCausalRowObserver.toAdaptive,
          V13RealLinearCausalRowObserver.staticBranch,
          v13RealLinearCausalSingleRowObserver] using cert.property w
      exact hcoeff.symm
  right_inv pair := by
    cases pair with
    | mk occ x =>
      apply Prod.ext
      · apply Subtype.ext
        rfl
      · rfl

theorem v13RealLinear_causalSingleRowGeneratedCoefficient_card_eq
    {m : Nat} (row i₀ : Fin m) :
    Fintype.card
        (V13RealLinearAdaptiveQRowGeneratedCoefficient
          (v13RealLinearUniformCausalQRowExperiment
            (v13RealLinearCausalSingleRowObserver row)) i₀) =
      Fintype.card (V13RealLinearUniformFixedTargetRowOccurrence row i₀) *
        Fintype.card (F2Vec m) := by
  classical
  rw [Fintype.card_congr
    (v13RealLinear_causalSingleRowGeneratedCoefficientEquivFixedOccurrenceProd
      row i₀)]
  simp [Fintype.card_prod]

/-- Fixed-row occurrence form of the constant single-row causal count.  It
asks that a specified public row equals the target row on at most a
`2 / 2^m` fraction of certified invertible maps, stated without division. -/
def V13RealLinearUniformFixedTargetRowOccurrenceCountingBound : Prop :=
  ∀ {m : Nat} (row i₀ : Fin m),
    Fintype.card (V13RealLinearUniformFixedTargetRowOccurrence row i₀) *
        2 ^ m ≤
      2 * Fintype.card (V13F2LinearEquiv m)

theorem v13RealLinearUniformFixedTargetRowOccurrenceCountingBound_proved :
    V13RealLinearUniformFixedTargetRowOccurrenceCountingBound := by
  intro m row i₀
  exact v13RealLinearFixedTargetRowOccurrence_counting row i₀

/-- Representative form of the constant single-row occurrence count.  Since
fixed-row occurrence cardinalities are invariant under coordinate swaps, it is
enough to prove the bound for one row/target pair in each nonempty dimension. -/
def V13RealLinearUniformRepresentativeFixedTargetRowOccurrenceCountingBound :
    Prop :=
  ∀ {m : Nat}, Nonempty (Fin m) →
    ∃ row i₀ : Fin m,
      Fintype.card (V13RealLinearUniformFixedTargetRowOccurrence row i₀) *
          2 ^ m ≤
        2 * Fintype.card (V13F2LinearEquiv m)

theorem
    V13RealLinearUniformRepresentativeFixedTargetRowOccurrenceCountingBound_of_fixed
    (hcount : V13RealLinearUniformFixedTargetRowOccurrenceCountingBound) :
    V13RealLinearUniformRepresentativeFixedTargetRowOccurrenceCountingBound := by
  classical
  intro m hnonempty
  let row : Fin m := Classical.choice hnonempty
  exact ⟨row, row, hcount row row⟩

theorem
    V13RealLinearUniformFixedTargetRowOccurrenceCountingBound_of_representative
    (hcount :
      V13RealLinearUniformRepresentativeFixedTargetRowOccurrenceCountingBound) :
    V13RealLinearUniformFixedTargetRowOccurrenceCountingBound := by
  classical
  intro m row i₀
  rcases hcount (m := m) ⟨row⟩ with ⟨row', i₀', hrep⟩
  have hcard :
      Fintype.card
          (V13RealLinearUniformFixedTargetRowOccurrence row i₀) =
        Fintype.card
          (V13RealLinearUniformFixedTargetRowOccurrence row' i₀') :=
    v13RealLinearFixedTargetRowOccurrence_card_eq_of_swap
      row row' i₀ i₀'
  rwa [hcard]

theorem V13RealLinearUniformFixedTargetRowOccurrenceCountingBound_iff_representative :
    V13RealLinearUniformFixedTargetRowOccurrenceCountingBound ↔
      V13RealLinearUniformRepresentativeFixedTargetRowOccurrenceCountingBound :=
  ⟨V13RealLinearUniformRepresentativeFixedTargetRowOccurrenceCountingBound_of_fixed,
    V13RealLinearUniformFixedTargetRowOccurrenceCountingBound_of_representative⟩

theorem
    v13RealLinearUniformRepresentativeFixedTargetRowOccurrenceCountingBound_proved :
    V13RealLinearUniformRepresentativeFixedTargetRowOccurrenceCountingBound :=
  V13RealLinearUniformRepresentativeFixedTargetRowOccurrenceCountingBound_of_fixed
    v13RealLinearUniformFixedTargetRowOccurrenceCountingBound_proved

theorem v13RealLinear_causalSingleRow_coefficientCounting_of_fixedTargetRowOccurrenceCounting
    (hcount : V13RealLinearUniformFixedTargetRowOccurrenceCountingBound)
    {m : Nat} (row i₀ : Fin m) :
    Fintype.card
        (V13RealLinearAdaptiveQRowGeneratedCoefficient
          (v13RealLinearUniformCausalQRowExperiment
            (v13RealLinearCausalSingleRowObserver row)) i₀) *
        2 ^ m ≤
      2 ^ 1 *
        Fintype.card
          (V13RealLinearAdaptiveQRowWorld m (V13F2LinearEquiv m)) := by
  classical
  rw [v13RealLinear_causalSingleRowGeneratedCoefficient_card_eq]
  rw [Fintype.card_prod, v13RealLinear_f2vec_card]
  let O := Fintype.card (V13RealLinearUniformFixedTargetRowOccurrence row i₀)
  let A := Fintype.card (V13F2LinearEquiv m)
  let X := 2 ^ m
  have hfixed : O * X ≤ 2 * A := by
    simpa [O, A, X] using hcount row i₀
  change (O * X) * X ≤ 2 * (A * X)
  nlinarith

theorem
    v13RealLinear_causalSingleRow_coefficientCounting_of_representativeFixedTargetRowOccurrenceCounting
    (hcount :
      V13RealLinearUniformRepresentativeFixedTargetRowOccurrenceCountingBound)
    {m : Nat} (row i₀ : Fin m) :
    Fintype.card
        (V13RealLinearAdaptiveQRowGeneratedCoefficient
          (v13RealLinearUniformCausalQRowExperiment
            (v13RealLinearCausalSingleRowObserver row)) i₀) *
        2 ^ m ≤
      2 ^ 1 *
        Fintype.card
          (V13RealLinearAdaptiveQRowWorld m (V13F2LinearEquiv m)) := by
  exact
    v13RealLinear_causalSingleRow_coefficientCounting_of_fixedTargetRowOccurrenceCounting
      (V13RealLinearUniformFixedTargetRowOccurrenceCountingBound_of_representative
        hcount)
      row i₀

theorem v13RealLinear_causalSingleRow_coefficientCounting
    {m : Nat} (row i₀ : Fin m) :
    Fintype.card
        (V13RealLinearAdaptiveQRowGeneratedCoefficient
          (v13RealLinearUniformCausalQRowExperiment
            (v13RealLinearCausalSingleRowObserver row)) i₀) *
        2 ^ m ≤
      2 ^ 1 *
        Fintype.card
          (V13RealLinearAdaptiveQRowWorld m (V13F2LinearEquiv m)) := by
  exact
    v13RealLinear_causalSingleRow_coefficientCounting_of_fixedTargetRowOccurrenceCounting
      v13RealLinearUniformFixedTargetRowOccurrenceCountingBound_proved
      row i₀

theorem v13RealLinear_causalSingleRow_generated_counting
    {m : Nat} (row i₀ : Fin m) :
    Fintype.card
        (V13RealLinearAdaptiveQRowGenerated
          (v13RealLinearUniformCausalQRowExperiment
            (v13RealLinearCausalSingleRowObserver row)) i₀) *
        2 ^ m ≤
      2 ^ 1 *
        Fintype.card
          (V13RealLinearAdaptiveQRowWorld m (V13F2LinearEquiv m)) := by
  classical
  let E :=
    v13RealLinearUniformCausalQRowExperiment
      (v13RealLinearCausalSingleRowObserver row)
  let G := Fintype.card (V13RealLinearAdaptiveQRowGenerated E i₀)
  let C :=
    Fintype.card (V13RealLinearAdaptiveQRowGeneratedCoefficient E i₀)
  let M := 2 ^ m
  have hG : G ≤ C := by
    simpa [G, C, E] using
      v13RealLinearAdaptiveQRowGenerated_card_le_coefficient E i₀
  have hC :
      C * M ≤
        2 ^ 1 *
          Fintype.card
            (V13RealLinearAdaptiveQRowWorld m (V13F2LinearEquiv m)) := by
    simpa [C, E, M] using
      v13RealLinear_causalSingleRow_coefficientCounting row i₀
  exact (Nat.mul_le_mul_right M hG).trans hC

theorem v13RealLinear_causalSingleRow_rowSpanCountingBound
    {m : Nat} (row i₀ : Fin m) :
    V13RealLinearUniformCausalRowSpanCountingBound
      (v13RealLinearCausalSingleRowObserver row) i₀ :=
  v13RealLinearUniformCausalRowSpanCountingBound_of_generated_counting
    (v13RealLinearCausalSingleRowObserver row) i₀
    (v13RealLinear_causalSingleRow_generated_counting row i₀)

theorem v13RealLinear_causalSingleRow_success_bound
    {m : Nat} (row i₀ : Fin m) :
    v13RealLinearUniformCausalQRowSuccess
        (v13RealLinearCausalSingleRowObserver row) i₀ ≤
      (1 / 2 : Rat) + v13RealLinearQRowEpsilon 1 m :=
  v13RealLinear_uniform_causal_qrow_success_bound_of_spanCounting
    (v13RealLinearCausalSingleRowObserver row) i₀
    (v13RealLinear_causalSingleRow_rowSpanCountingBound row i₀)

theorem v13RealLinear_fixedTargetRowOccurrence_zero_two_counting :
    Fintype.card
        (V13RealLinearUniformFixedTargetRowOccurrence
          (0 : Fin 2) (0 : Fin 2)) *
        2 ^ 2 ≤
      2 * Fintype.card (V13F2LinearEquiv 2) := by
  classical
  let O :=
    Fintype.card
      (V13RealLinearUniformFixedTargetRowOccurrence
        (0 : Fin 2) (0 : Fin 2))
  let A := Fintype.card (V13F2LinearEquiv 2)
  change O * 4 ≤ 2 * A
  have hO : O ≤ 2 := by
    exact v13RealLinearFixedTargetRowOccurrence_zero_card_le_two
  have hA : 4 ≤ A := by
    exact v13RealLinear_f2_equiv_two_card_four_le
  nlinarith

theorem v13RealLinear_fixedTargetRowOccurrence_two_counting
    (row i₀ : Fin 2) :
    Fintype.card
        (V13RealLinearUniformFixedTargetRowOccurrence row i₀) *
        2 ^ 2 ≤
      2 * Fintype.card (V13F2LinearEquiv 2) := by
  classical
  let O := Fintype.card (V13RealLinearUniformFixedTargetRowOccurrence row i₀)
  let A := Fintype.card (V13F2LinearEquiv 2)
  change O * 4 ≤ 2 * A
  have hO : O ≤ 2 := by
    exact v13RealLinearFixedTargetRowOccurrence_two_card_le_two row i₀
  have hA : 4 ≤ A := by
    exact v13RealLinear_f2_equiv_two_card_four_le
  nlinarith

theorem v13RealLinear_causalSingleRow_zero_two_coefficientCounting :
    Fintype.card
        (V13RealLinearAdaptiveQRowGeneratedCoefficient
          (v13RealLinearUniformCausalQRowExperiment
            (v13RealLinearCausalSingleRowObserver (0 : Fin 2)))
          (0 : Fin 2)) *
        2 ^ 2 ≤
      2 ^ 1 *
        Fintype.card
          (V13RealLinearAdaptiveQRowWorld 2 (V13F2LinearEquiv 2)) := by
  classical
  rw [v13RealLinear_causalSingleRowGeneratedCoefficient_card_eq]
  rw [Fintype.card_prod, v13RealLinear_f2vec_card]
  let O :=
    Fintype.card
      (V13RealLinearUniformFixedTargetRowOccurrence
        (0 : Fin 2) (0 : Fin 2))
  let A := Fintype.card (V13F2LinearEquiv 2)
  change (O * 4) * 4 ≤ 2 * (A * 4)
  have hO : O ≤ 2 := by
    exact v13RealLinearFixedTargetRowOccurrence_zero_card_le_two
  have hA : 4 ≤ A := by
    exact v13RealLinear_f2_equiv_two_card_four_le
  nlinarith

theorem v13RealLinear_causalSingleRow_two_coefficientCounting
    (row i₀ : Fin 2) :
    Fintype.card
        (V13RealLinearAdaptiveQRowGeneratedCoefficient
          (v13RealLinearUniformCausalQRowExperiment
            (v13RealLinearCausalSingleRowObserver row)) i₀) *
        2 ^ 2 ≤
      2 ^ 1 *
        Fintype.card
          (V13RealLinearAdaptiveQRowWorld 2 (V13F2LinearEquiv 2)) := by
  classical
  rw [v13RealLinear_causalSingleRowGeneratedCoefficient_card_eq]
  rw [Fintype.card_prod, v13RealLinear_f2vec_card]
  let O := Fintype.card (V13RealLinearUniformFixedTargetRowOccurrence row i₀)
  let A := Fintype.card (V13F2LinearEquiv 2)
  change (O * 4) * 4 ≤ 2 * (A * 4)
  have hcount : O * 4 ≤ 2 * A := by
    simpa [O, A] using
      v13RealLinear_fixedTargetRowOccurrence_two_counting row i₀
  nlinarith

noncomputable def v13RealLinearCausalSingleRowIdentityFiberEmbedding :
    F2Vec 2 ↪
      V13RealLinearAdaptiveQRowGeneratedCoefficientFiber
        (v13RealLinearUniformCausalQRowExperiment
          (v13RealLinearCausalSingleRowObserver (0 : Fin 2)))
        (0 : Fin 2) (v13RealLinearIdentity 2) where
  toFun x :=
    ⟨⟨x, fun _ => 1⟩, by
      intro w
      simp [v13RealLinearUniformCausalQRowExperiment,
        v13RealLinearUniformQRowExperiment,
        V13RealLinearAdaptiveQRowExperiment.branchRows,
        V13RealLinearAdaptiveQRowExperiment.branch,
        V13RealLinearCausalRowObserver.toAdaptive,
        V13RealLinearCausalRowObserver.staticBranch,
        v13RealLinearCausalSingleRowObserver,
        v13RealLinearRowCombinationEval, v13RealLinearIdentity]⟩
  inj' := by
    intro x y hxy
    exact
      congrArg
        (fun cert :
          V13RealLinearAdaptiveQRowGeneratedCoefficientFiber
            (v13RealLinearUniformCausalQRowExperiment
              (v13RealLinearCausalSingleRowObserver (0 : Fin 2)))
            (0 : Fin 2) (v13RealLinearIdentity 2) =>
          cert.val.1)
        hxy

theorem v13RealLinearCausalSingleRowIdentityFiber_card_four_le :
    4 ≤
      Fintype.card
        (V13RealLinearAdaptiveQRowGeneratedCoefficientFiber
          (v13RealLinearUniformCausalQRowExperiment
            (v13RealLinearCausalSingleRowObserver (0 : Fin 2)))
          (0 : Fin 2) (v13RealLinearIdentity 2)) := by
  classical
  have hle :
      Fintype.card (F2Vec 2) ≤
        Fintype.card
          (V13RealLinearAdaptiveQRowGeneratedCoefficientFiber
            (v13RealLinearUniformCausalQRowExperiment
              (v13RealLinearCausalSingleRowObserver (0 : Fin 2)))
            (0 : Fin 2) (v13RealLinearIdentity 2)) :=
    Fintype.card_le_of_embedding
      v13RealLinearCausalSingleRowIdentityFiberEmbedding
  have hcard : Fintype.card (F2Vec 2) = 4 := by
    rw [v13RealLinear_f2vec_card]
    norm_num
  simpa [hcard] using hle

theorem v13RealLinearUniformCausalLowPositiveFiberCoefficientCountingBound_fails_two_identity :
    ¬ V13RealLinearUniformCausalLowPositiveFiberCoefficientCountingBound := by
  intro hcount
  have hle :=
    hcount (v13RealLinearCausalSingleRowObserver (0 : Fin 2))
      (0 : Fin 2) (by norm_num) (by norm_num) (v13RealLinearIdentity 2)
  have hfour :=
    v13RealLinearCausalSingleRowIdentityFiber_card_four_le
  norm_num at hle
  omega

theorem v13RealLinearUniformCausalLowPositiveCoefficientCountingBound_of_fiberCounting
    (hcount :
      V13RealLinearUniformCausalLowPositiveFiberCoefficientCountingBound) :
    V13RealLinearUniformCausalLowPositiveCoefficientCountingBound := by
  intro m q observer i₀ hqpos hqm
  let E := v13RealLinearUniformCausalQRowExperiment observer
  let C :=
    Fintype.card (V13RealLinearAdaptiveQRowGeneratedCoefficient E i₀)
  let S := Fintype.card (V13F2LinearEquiv m)
  let M := 2 ^ m
  let Q := 2 ^ q
  have hCeq :
      C =
        ∑ A : V13F2LinearEquiv m,
          Fintype.card
            (V13RealLinearAdaptiveQRowGeneratedCoefficientFiber E i₀ A) := by
    simpa [C, E] using
      v13RealLinearAdaptiveQRowGeneratedCoefficient_card_eq_sum_fibers
        (v13RealLinearUniformCausalQRowExperiment observer) i₀
  have hsum :
      (∑ A : V13F2LinearEquiv m,
          Fintype.card
            (V13RealLinearAdaptiveQRowGeneratedCoefficientFiber E i₀ A)) ≤
        ∑ _A : V13F2LinearEquiv m, Q := by
    exact
      Finset.sum_le_sum
        (fun A _hA => by
          dsimp [Q, E]
          exact hcount observer i₀ hqpos hqm A)
  have hsumConst :
      (∑ _A : V13F2LinearEquiv m, Q) = S * Q := by
    simp [S]
  have hCbound : C ≤ S * Q := by
    rw [hCeq]
    exact hsum.trans_eq hsumConst
  have hworld :
      Fintype.card
          (V13RealLinearAdaptiveQRowWorld m (V13F2LinearEquiv m)) =
        S * M := by
    dsimp [V13RealLinearAdaptiveQRowWorld, S, M]
    rw [Fintype.card_prod]
    rw [v13RealLinear_f2vec_card m]
  have hmain : C * M ≤ Q * (S * M) := by
    calc
      C * M ≤ (S * Q) * M := Nat.mul_le_mul_right M hCbound
      _ = Q * (S * M) := by ring
  simpa [C, E, M, Q, hworld] using hmain

theorem v13RealLinearUniformCausalLowPositiveCompletionCountingBound_of_coefficientCounting
    (hcount :
      V13RealLinearUniformCausalLowPositiveCoefficientCountingBound) :
    V13RealLinearUniformCausalLowPositiveCompletionCountingBound := by
  intro m q observer i₀ hqpos hqm
  let E := v13RealLinearUniformCausalQRowExperiment observer
  let G := Fintype.card (V13RealLinearAdaptiveQRowGenerated E i₀)
  let C :=
    Fintype.card (V13RealLinearAdaptiveQRowGeneratedCoefficient E i₀)
  let M := 2 ^ m
  let Q := 2 ^ q
  let T := Fintype.card
    (V13RealLinearAdaptiveQRowWorld m (V13F2LinearEquiv m))
  have hgenCoeff : G ≤ C := by
    dsimp [G, C, E]
    exact
      v13RealLinearAdaptiveQRowGenerated_card_le_coefficient
        (v13RealLinearUniformCausalQRowExperiment observer) i₀
  have hmul : G * M ≤ C * M :=
    Nat.mul_le_mul_right M hgenCoeff
  have hcert : C * M ≤ Q * T := by
    simpa [E, G, C, M, Q, T] using hcount observer i₀ hqpos hqm
  exact hmul.trans hcert

theorem v13RealLinearUniformCausalLowPositiveRowSpanCountingBound_of_completionCounting
    (hcount :
      V13RealLinearUniformCausalLowPositiveCompletionCountingBound) :
    V13RealLinearUniformCausalLowPositiveRowSpanCountingBound := by
  intro m q observer i₀ hqpos hqm
  unfold V13RealLinearUniformCausalRowSpanCountingBound
  unfold V13RealLinearAdaptiveRowSpanCountingBound
  unfold v13RealLinearAdaptiveQRowGeneratedMass
  unfold v13RealLinearQRowEpsilon
  let G := Fintype.card
    (V13RealLinearAdaptiveQRowGenerated
      (v13RealLinearUniformCausalQRowExperiment observer) i₀)
  let T := Fintype.card
    (V13RealLinearAdaptiveQRowWorld m (V13F2LinearEquiv m))
  let Q := 2 ^ q
  let M := 2 ^ m
  have hcard : G * M ≤ Q * T := by
    simpa [G, T, Q, M] using hcount observer i₀ hqpos hqm
  have hTposNat : 0 < T := by
    dsimp [T]
    exact Fintype.card_pos_iff.mpr ⟨(v13RealLinearIdentity m, f2ZeroVec m)⟩
  have hMposNat : 0 < M := by
    dsimp [M]
    positivity
  have hTpos : (0 : Rat) < (T : Rat) := by
    exact_mod_cast hTposNat
  have hMpos : (0 : Rat) < (M : Rat) := by
    exact_mod_cast hMposNat
  have hcardRat : (G : Rat) * (M : Rat) ≤ (Q : Rat) * (T : Rat) := by
    exact_mod_cast hcard
  have hQrat : (2 : Rat) ^ q = (Q : Rat) := by
    dsimp [Q]
    norm_num
  have hMrat : (2 : Rat) ^ m = (M : Rat) := by
    dsimp [M]
    norm_num
  rw [hQrat, hMrat]
  change (G : Rat) / (T : Rat) ≤ (Q : Rat) / (M : Rat)
  rw [div_le_div_iff₀ hTpos hMpos]
  exact hcardRat

theorem v13RealLinearUniformCausalLowPositiveCompletionCountingBound_of_rowSpanCounting
    (hcount :
      V13RealLinearUniformCausalLowPositiveRowSpanCountingBound) :
    V13RealLinearUniformCausalLowPositiveCompletionCountingBound := by
  intro m q observer i₀ hqpos hqm
  have hmass := hcount observer i₀ hqpos hqm
  unfold V13RealLinearUniformCausalRowSpanCountingBound at hmass
  unfold V13RealLinearAdaptiveRowSpanCountingBound at hmass
  unfold v13RealLinearAdaptiveQRowGeneratedMass at hmass
  unfold v13RealLinearQRowEpsilon at hmass
  let G := Fintype.card
    (V13RealLinearAdaptiveQRowGenerated
      (v13RealLinearUniformCausalQRowExperiment observer) i₀)
  let T := Fintype.card
    (V13RealLinearAdaptiveQRowWorld m (V13F2LinearEquiv m))
  let Q := 2 ^ q
  let M := 2 ^ m
  have hTposNat : 0 < T := by
    dsimp [T]
    exact Fintype.card_pos_iff.mpr ⟨(v13RealLinearIdentity m, f2ZeroVec m)⟩
  have hMposNat : 0 < M := by
    dsimp [M]
    positivity
  have hTpos : (0 : Rat) < (T : Rat) := by
    exact_mod_cast hTposNat
  have hMpos : (0 : Rat) < (M : Rat) := by
    exact_mod_cast hMposNat
  have hQrat : (2 : Rat) ^ q = (Q : Rat) := by
    dsimp [Q]
    norm_num
  have hMrat : (2 : Rat) ^ m = (M : Rat) := by
    dsimp [M]
    norm_num
  have hmass' :
      (G : Rat) / (T : Rat) ≤ (Q : Rat) / (M : Rat) := by
    change (G : Rat) / (T : Rat) ≤ (2 : Rat) ^ q / (2 : Rat) ^ m at hmass
    rw [hQrat, hMrat] at hmass
    exact hmass
  have hcardRat : (G : Rat) * (M : Rat) ≤ (Q : Rat) * (T : Rat) := by
    exact (div_le_div_iff₀ hTpos hMpos).1 hmass'
  have hcardNat : G * M ≤ Q * T := by
    exact_mod_cast hcardRat
  simpa [G, T, Q, M] using hcardNat

theorem V13RealLinearUniformCausalLowPositiveRowSpanCountingBound_iff_completionCounting :
    V13RealLinearUniformCausalLowPositiveRowSpanCountingBound ↔
      V13RealLinearUniformCausalLowPositiveCompletionCountingBound :=
  ⟨v13RealLinearUniformCausalLowPositiveCompletionCountingBound_of_rowSpanCounting,
    v13RealLinearUniformCausalLowPositiveRowSpanCountingBound_of_completionCounting⟩

theorem
    V13RealLinearUniformCausalLowPositiveRowSpanCountingBound_of_twoOrMore
    (hcount :
      ∀ {m q : Nat} (observer : V13RealLinearCausalRowObserver m q)
        (i₀ : Fin m),
        1 < q → q < m →
          V13RealLinearUniformCausalRowSpanCountingBound observer i₀) :
    V13RealLinearUniformCausalLowPositiveRowSpanCountingBound := by
  intro m q observer i₀ hqpos hqm
  by_cases hqle : q ≤ 1
  · have hq : q = 1 := by omega
    subst q
    exact
      v13RealLinearUniformCausalOneRowRowSpanCountingBound_proved
        observer i₀ hqm
  · exact hcount observer i₀ (by omega) hqm

theorem
    V13RealLinearUniformCausalLowPositiveRowSpanCountingBound_of_twoOrMoreBound
    (hcount :
      V13RealLinearUniformCausalTwoOrMoreRowSpanCountingBound) :
    V13RealLinearUniformCausalLowPositiveRowSpanCountingBound :=
  V13RealLinearUniformCausalLowPositiveRowSpanCountingBound_of_twoOrMore
    hcount

theorem
    V13RealLinearUniformCausalTwoOrMoreRowSpanCountingBound_of_lowPositive
    (hcount :
      V13RealLinearUniformCausalLowPositiveRowSpanCountingBound) :
    V13RealLinearUniformCausalTwoOrMoreRowSpanCountingBound := by
  intro m q observer i₀ hqgt hqm
  exact hcount observer i₀ (by omega) hqm

theorem
    V13RealLinearUniformCausalLowPositiveRowSpanCountingBound_iff_twoOrMore :
    V13RealLinearUniformCausalLowPositiveRowSpanCountingBound ↔
      V13RealLinearUniformCausalTwoOrMoreRowSpanCountingBound :=
  ⟨V13RealLinearUniformCausalTwoOrMoreRowSpanCountingBound_of_lowPositive,
    V13RealLinearUniformCausalLowPositiveRowSpanCountingBound_of_twoOrMoreBound⟩

theorem
    V13RealLinearUniformCausalLowPositiveCompletionCountingBound_of_twoOrMore
    (hcount :
      ∀ {m q : Nat} (observer : V13RealLinearCausalRowObserver m q)
        (i₀ : Fin m),
        1 < q → q < m →
          Fintype.card
              (V13RealLinearAdaptiveQRowGenerated
                (v13RealLinearUniformCausalQRowExperiment observer) i₀) *
            2 ^ m ≤
          2 ^ q *
            Fintype.card
              (V13RealLinearAdaptiveQRowWorld m (V13F2LinearEquiv m))) :
    V13RealLinearUniformCausalLowPositiveCompletionCountingBound := by
  intro m q observer i₀ hqpos hqm
  by_cases hqle : q ≤ 1
  · have hq : q = 1 := by omega
    subst q
    exact
      v13RealLinearUniformCausalOneRowGenerated_counting_proved
        observer i₀ hqm
  · exact hcount observer i₀ (by omega) hqm

theorem
    V13RealLinearUniformCausalLowPositiveCompletionCountingBound_of_twoOrMoreBound
    (hcount :
      V13RealLinearUniformCausalTwoOrMoreCompletionCountingBound) :
    V13RealLinearUniformCausalLowPositiveCompletionCountingBound :=
  V13RealLinearUniformCausalLowPositiveCompletionCountingBound_of_twoOrMore
    hcount

theorem
    V13RealLinearUniformCausalTwoOrMoreCompletionCountingBound_of_lowPositive
    (hcount :
      V13RealLinearUniformCausalLowPositiveCompletionCountingBound) :
    V13RealLinearUniformCausalTwoOrMoreCompletionCountingBound := by
  intro m q observer i₀ hqgt hqm
  exact hcount observer i₀ (by omega) hqm

theorem
    V13RealLinearUniformCausalLowPositiveCompletionCountingBound_iff_twoOrMore :
    V13RealLinearUniformCausalLowPositiveCompletionCountingBound ↔
      V13RealLinearUniformCausalTwoOrMoreCompletionCountingBound :=
  ⟨V13RealLinearUniformCausalTwoOrMoreCompletionCountingBound_of_lowPositive,
    V13RealLinearUniformCausalLowPositiveCompletionCountingBound_of_twoOrMoreBound⟩

theorem
    V13RealLinearUniformCausalTwoOrMoreCompletionCountingBound_of_coefficientCounting
    (hcount :
      V13RealLinearUniformCausalTwoOrMoreCoefficientCountingBound) :
    V13RealLinearUniformCausalTwoOrMoreCompletionCountingBound := by
  intro m q observer i₀ hqgt hqm
  let E := v13RealLinearUniformCausalQRowExperiment observer
  let G := Fintype.card (V13RealLinearAdaptiveQRowGenerated E i₀)
  let C :=
    Fintype.card (V13RealLinearAdaptiveQRowGeneratedCoefficient E i₀)
  let M := 2 ^ m
  let Q := 2 ^ q
  let T := Fintype.card
    (V13RealLinearAdaptiveQRowWorld m (V13F2LinearEquiv m))
  have hgenCoeff : G ≤ C := by
    dsimp [G, C, E]
    exact
      v13RealLinearAdaptiveQRowGenerated_card_le_coefficient
        (v13RealLinearUniformCausalQRowExperiment observer) i₀
  have hmul : G * M ≤ C * M :=
    Nat.mul_le_mul_right M hgenCoeff
  have hcert : C * M ≤ Q * T := by
    simpa [E, G, C, M, Q, T] using hcount observer i₀ hqgt hqm
  exact hmul.trans hcert

theorem
    V13RealLinearUniformCausalLowPositiveCompletionCountingBound_of_twoOrMoreCoefficientCounting
    (hcount :
      V13RealLinearUniformCausalTwoOrMoreCoefficientCountingBound) :
    V13RealLinearUniformCausalLowPositiveCompletionCountingBound :=
  V13RealLinearUniformCausalLowPositiveCompletionCountingBound_of_twoOrMoreBound
    (V13RealLinearUniformCausalTwoOrMoreCompletionCountingBound_of_coefficientCounting
      hcount)

theorem
    V13RealLinearUniformCausalTwoOrMoreCoefficientCountingBound_of_compression
    (hcount :
      V13RealLinearUniformCausalTwoOrMoreCoefficientCompressionBound) :
    V13RealLinearUniformCausalTwoOrMoreCoefficientCountingBound := by
  intro m q observer i₀ hqgt hqm
  let E := v13RealLinearUniformCausalQRowExperiment observer
  let C :=
    Fintype.card (V13RealLinearAdaptiveQRowGeneratedCoefficient E i₀)
  let S := Fintype.card (V13F2LinearEquiv m)
  let M := 2 ^ m
  let Q := 2 ^ q
  have hC : C ≤ Q * S := by
    simpa [C, E, Q, S] using hcount observer i₀ hqgt hqm
  have hworld :
      Fintype.card
          (V13RealLinearAdaptiveQRowWorld m (V13F2LinearEquiv m)) =
        S * M := by
    dsimp [V13RealLinearAdaptiveQRowWorld, S, M]
    rw [Fintype.card_prod]
    rw [v13RealLinear_f2vec_card m]
  have hmain : C * M ≤ Q * (S * M) := by
    calc
      C * M ≤ (Q * S) * M := Nat.mul_le_mul_right M hC
      _ = Q * (S * M) := by ring
  simpa [C, E, M, Q, hworld] using hmain

theorem
    V13RealLinearUniformCausalTwoOrMoreCoefficientCompressionBound_of_counting
    (hcount :
      V13RealLinearUniformCausalTwoOrMoreCoefficientCountingBound) :
    V13RealLinearUniformCausalTwoOrMoreCoefficientCompressionBound := by
  intro m q observer i₀ hqgt hqm
  let E := v13RealLinearUniformCausalQRowExperiment observer
  let C :=
    Fintype.card (V13RealLinearAdaptiveQRowGeneratedCoefficient E i₀)
  let S := Fintype.card (V13F2LinearEquiv m)
  let M := 2 ^ m
  let Q := 2 ^ q
  have hworld :
      Fintype.card
          (V13RealLinearAdaptiveQRowWorld m (V13F2LinearEquiv m)) =
        S * M := by
    dsimp [V13RealLinearAdaptiveQRowWorld, S, M]
    rw [Fintype.card_prod]
    rw [v13RealLinear_f2vec_card m]
  have hcount' : C * M ≤ (Q * S) * M := by
    have hraw : C * M ≤ Q * (S * M) := by
      simpa [C, E, M, Q, hworld] using hcount observer i₀ hqgt hqm
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hraw
  have hMpos : 0 < M := by
    dsimp [M]
    positivity
  exact Nat.le_of_mul_le_mul_right hcount' hMpos

theorem
    V13RealLinearUniformCausalTwoOrMoreCoefficientCountingBound_iff_compression :
    V13RealLinearUniformCausalTwoOrMoreCoefficientCountingBound ↔
      V13RealLinearUniformCausalTwoOrMoreCoefficientCompressionBound :=
  ⟨V13RealLinearUniformCausalTwoOrMoreCoefficientCompressionBound_of_counting,
    V13RealLinearUniformCausalTwoOrMoreCoefficientCountingBound_of_compression⟩

theorem
    V13RealLinearUniformCausalTwoOrMoreCompletionCountingBound_of_coefficientCompression
    (hcount :
      V13RealLinearUniformCausalTwoOrMoreCoefficientCompressionBound) :
    V13RealLinearUniformCausalTwoOrMoreCompletionCountingBound :=
  V13RealLinearUniformCausalTwoOrMoreCompletionCountingBound_of_coefficientCounting
    (V13RealLinearUniformCausalTwoOrMoreCoefficientCountingBound_of_compression
      hcount)

theorem
    V13RealLinearUniformCausalTwoOrMoreCoefficientCompressionBound_of_fiberAverage
    (hcount :
      V13RealLinearUniformCausalTwoOrMoreFiberAverageCoefficientBound) :
    V13RealLinearUniformCausalTwoOrMoreCoefficientCompressionBound := by
  intro m q observer i₀ hqgt hqm
  let E := v13RealLinearUniformCausalQRowExperiment observer
  let C :=
    Fintype.card (V13RealLinearAdaptiveQRowGeneratedCoefficient E i₀)
  let Q := 2 ^ q
  let S := Fintype.card (V13F2LinearEquiv m)
  have hCeq :
      C =
        ∑ A : V13F2LinearEquiv m,
          Fintype.card
            (V13RealLinearAdaptiveQRowGeneratedCoefficientFiber E i₀ A) := by
    simpa [C, E] using
      v13RealLinearAdaptiveQRowGeneratedCoefficient_card_eq_sum_fibers
        (v13RealLinearUniformCausalQRowExperiment observer) i₀
  have hsum :
      (∑ A : V13F2LinearEquiv m,
          Fintype.card
            (V13RealLinearAdaptiveQRowGeneratedCoefficientFiber E i₀ A)) ≤
        Q * S := by
    simpa [E, Q, S] using hcount observer i₀ hqgt hqm
  calc
    C =
        ∑ A : V13F2LinearEquiv m,
          Fintype.card
            (V13RealLinearAdaptiveQRowGeneratedCoefficientFiber E i₀ A) :=
      hCeq
    _ ≤ Q * S := hsum

theorem
    V13RealLinearUniformCausalTwoOrMoreFiberAverageCoefficientBound_of_compression
    (hcount :
      V13RealLinearUniformCausalTwoOrMoreCoefficientCompressionBound) :
    V13RealLinearUniformCausalTwoOrMoreFiberAverageCoefficientBound := by
  intro m q observer i₀ hqgt hqm
  let E := v13RealLinearUniformCausalQRowExperiment observer
  let C :=
    Fintype.card (V13RealLinearAdaptiveQRowGeneratedCoefficient E i₀)
  let Q := 2 ^ q
  let S := Fintype.card (V13F2LinearEquiv m)
  have hCeq :
      C =
        ∑ A : V13F2LinearEquiv m,
          Fintype.card
            (V13RealLinearAdaptiveQRowGeneratedCoefficientFiber E i₀ A) := by
    simpa [C, E] using
      v13RealLinearAdaptiveQRowGeneratedCoefficient_card_eq_sum_fibers
        (v13RealLinearUniformCausalQRowExperiment observer) i₀
  have hC : C ≤ Q * S := by
    simpa [C, E, Q, S] using hcount observer i₀ hqgt hqm
  calc
    (∑ A : V13F2LinearEquiv m,
        Fintype.card
          (V13RealLinearAdaptiveQRowGeneratedCoefficientFiber E i₀ A)) =
        C := hCeq.symm
    _ ≤ Q * S := hC

theorem
    V13RealLinearUniformCausalTwoOrMoreCoefficientCompressionBound_iff_fiberAverage :
    V13RealLinearUniformCausalTwoOrMoreCoefficientCompressionBound ↔
      V13RealLinearUniformCausalTwoOrMoreFiberAverageCoefficientBound :=
  ⟨V13RealLinearUniformCausalTwoOrMoreFiberAverageCoefficientBound_of_compression,
    V13RealLinearUniformCausalTwoOrMoreCoefficientCompressionBound_of_fiberAverage⟩

theorem
    V13RealLinearUniformCausalTwoOrMoreTargetCoefficientFiberAverageBound_of_fiberAverageCoefficient
    (hcount :
      V13RealLinearUniformCausalTwoOrMoreFiberAverageCoefficientBound) :
    V13RealLinearUniformCausalTwoOrMoreTargetCoefficientFiberAverageBound := by
  intro m q observer i₀ hqgt hqm
  let E := v13RealLinearUniformCausalQRowExperiment observer
  let Q := 2 ^ q
  let S := Fintype.card (V13F2LinearEquiv m)
  have hsum :
      (∑ A : V13F2LinearEquiv m,
        Fintype.card
          (V13RealLinearAdaptiveQRowGeneratedCoefficientFiber E i₀ A)) ≤
      Q * S := by
    simpa [E, Q, S] using hcount observer i₀ hqgt hqm
  calc
    (∑ A : V13F2LinearEquiv m,
        Fintype.card
          (V13RealLinearAdaptiveQRowGeneratedTargetCoefficientFiber E i₀ A)) =
        ∑ A : V13F2LinearEquiv m,
          Fintype.card
            (V13RealLinearAdaptiveQRowGeneratedCoefficientFiber E i₀ A) := by
      apply Finset.sum_congr rfl
      intro A _
      exact
        (v13RealLinearAdaptiveQRowGeneratedCoefficientFiber_card_eq_targetCoefficientFiber
          E i₀ A).symm
    _ ≤ Q * S := hsum

theorem
    V13RealLinearUniformCausalTwoOrMoreFiberAverageCoefficientBound_of_targetCoefficientFiberAverage
    (hcount :
      V13RealLinearUniformCausalTwoOrMoreTargetCoefficientFiberAverageBound) :
    V13RealLinearUniformCausalTwoOrMoreFiberAverageCoefficientBound := by
  intro m q observer i₀ hqgt hqm
  let E := v13RealLinearUniformCausalQRowExperiment observer
  let Q := 2 ^ q
  let S := Fintype.card (V13F2LinearEquiv m)
  have hsum :
      (∑ A : V13F2LinearEquiv m,
        Fintype.card
          (V13RealLinearAdaptiveQRowGeneratedTargetCoefficientFiber E i₀ A)) ≤
      Q * S := by
    simpa [E, Q, S] using hcount observer i₀ hqgt hqm
  calc
    (∑ A : V13F2LinearEquiv m,
        Fintype.card
          (V13RealLinearAdaptiveQRowGeneratedCoefficientFiber E i₀ A)) =
        ∑ A : V13F2LinearEquiv m,
          Fintype.card
            (V13RealLinearAdaptiveQRowGeneratedTargetCoefficientFiber E i₀ A) := by
      apply Finset.sum_congr rfl
      intro A _
      exact
        v13RealLinearAdaptiveQRowGeneratedCoefficientFiber_card_eq_targetCoefficientFiber
          E i₀ A
    _ ≤ Q * S := hsum

theorem
    V13RealLinearUniformCausalTwoOrMoreFiberAverageCoefficientBound_iff_targetCoefficientFiberAverage :
    V13RealLinearUniformCausalTwoOrMoreFiberAverageCoefficientBound ↔
      V13RealLinearUniformCausalTwoOrMoreTargetCoefficientFiberAverageBound :=
  ⟨V13RealLinearUniformCausalTwoOrMoreTargetCoefficientFiberAverageBound_of_fiberAverageCoefficient,
    V13RealLinearUniformCausalTwoOrMoreFiberAverageCoefficientBound_of_targetCoefficientFiberAverage⟩

theorem
    V13RealLinearUniformCausalTwoOrMoreCoefficientCompressionBound_of_targetCoefficientFiberAverage
    (hcount :
      V13RealLinearUniformCausalTwoOrMoreTargetCoefficientFiberAverageBound) :
    V13RealLinearUniformCausalTwoOrMoreCoefficientCompressionBound :=
  V13RealLinearUniformCausalTwoOrMoreCoefficientCompressionBound_of_fiberAverage
    (V13RealLinearUniformCausalTwoOrMoreFiberAverageCoefficientBound_of_targetCoefficientFiberAverage
      hcount)

theorem
    V13RealLinearUniformCausalTwoOrMoreCompletionCountingBound_of_targetCoefficientFiberAverage
    (hcount :
      V13RealLinearUniformCausalTwoOrMoreTargetCoefficientFiberAverageBound) :
    V13RealLinearUniformCausalTwoOrMoreCompletionCountingBound :=
  V13RealLinearUniformCausalTwoOrMoreCompletionCountingBound_of_coefficientCompression
    (V13RealLinearUniformCausalTwoOrMoreCoefficientCompressionBound_of_targetCoefficientFiberAverage
      hcount)

theorem
    V13RealLinearUniformCausalTwoOrMoreTargetCoefficientRowsetAverageBound_of_targetCoefficientFiberAverage
    (hcount :
      V13RealLinearUniformCausalTwoOrMoreTargetCoefficientFiberAverageBound) :
    V13RealLinearUniformCausalTwoOrMoreTargetCoefficientRowsetAverageBound := by
  intro m q observer i₀ hqgt hqm
  let E := v13RealLinearUniformCausalQRowExperiment observer
  let Q := 2 ^ q
  let S := Fintype.card (V13F2LinearEquiv m)
  have hsum :
      (∑ A : V13F2LinearEquiv m,
        Fintype.card
          (V13RealLinearAdaptiveQRowGeneratedTargetCoefficientFiber
            E i₀ A)) ≤
      Q * S := by
    simpa [E, Q, S] using hcount observer i₀ hqgt hqm
  calc
    (∑ A : V13F2LinearEquiv m,
        ∑ rows : Finset (Fin m),
          Fintype.card
            (V13RealLinearAdaptiveQRowGeneratedTargetCoefficientRowsetCell
              E i₀ A rows)) =
        ∑ A : V13F2LinearEquiv m,
          Fintype.card
            (V13RealLinearAdaptiveQRowGeneratedTargetCoefficientFiber
              E i₀ A) := by
      apply Finset.sum_congr rfl
      intro A _
      exact
        (v13RealLinearAdaptiveQRowGeneratedTargetCoefficientFiber_card_eq_sum_rowsetCells
          E i₀ A).symm
    _ ≤ Q * S := hsum

theorem
    V13RealLinearUniformCausalTwoOrMoreTargetCoefficientFiberAverageBound_of_rowsetAverage
    (hcount :
      V13RealLinearUniformCausalTwoOrMoreTargetCoefficientRowsetAverageBound) :
    V13RealLinearUniformCausalTwoOrMoreTargetCoefficientFiberAverageBound := by
  intro m q observer i₀ hqgt hqm
  let E := v13RealLinearUniformCausalQRowExperiment observer
  let Q := 2 ^ q
  let S := Fintype.card (V13F2LinearEquiv m)
  have hsum :
      (∑ A : V13F2LinearEquiv m,
        ∑ rows : Finset (Fin m),
          Fintype.card
            (V13RealLinearAdaptiveQRowGeneratedTargetCoefficientRowsetCell
              E i₀ A rows)) ≤
      Q * S := by
    simpa [E, Q, S] using hcount observer i₀ hqgt hqm
  calc
    (∑ A : V13F2LinearEquiv m,
        Fintype.card
          (V13RealLinearAdaptiveQRowGeneratedTargetCoefficientFiber
            E i₀ A)) =
        ∑ A : V13F2LinearEquiv m,
          ∑ rows : Finset (Fin m),
            Fintype.card
              (V13RealLinearAdaptiveQRowGeneratedTargetCoefficientRowsetCell
                E i₀ A rows) := by
      apply Finset.sum_congr rfl
      intro A _
      exact
        v13RealLinearAdaptiveQRowGeneratedTargetCoefficientFiber_card_eq_sum_rowsetCells
          E i₀ A
    _ ≤ Q * S := hsum

theorem
    V13RealLinearUniformCausalTwoOrMoreTargetCoefficientFiberAverageBound_iff_rowsetAverage :
    V13RealLinearUniformCausalTwoOrMoreTargetCoefficientFiberAverageBound ↔
      V13RealLinearUniformCausalTwoOrMoreTargetCoefficientRowsetAverageBound :=
  ⟨V13RealLinearUniformCausalTwoOrMoreTargetCoefficientRowsetAverageBound_of_targetCoefficientFiberAverage,
    V13RealLinearUniformCausalTwoOrMoreTargetCoefficientFiberAverageBound_of_rowsetAverage⟩

theorem
    V13RealLinearUniformCausalTwoOrMoreCoefficientCompressionBound_of_targetCoefficientRowsetAverage
    (hcount :
      V13RealLinearUniformCausalTwoOrMoreTargetCoefficientRowsetAverageBound) :
    V13RealLinearUniformCausalTwoOrMoreCoefficientCompressionBound :=
  V13RealLinearUniformCausalTwoOrMoreCoefficientCompressionBound_of_targetCoefficientFiberAverage
    (V13RealLinearUniformCausalTwoOrMoreTargetCoefficientFiberAverageBound_of_rowsetAverage
      hcount)

theorem
    V13RealLinearUniformCausalTwoOrMoreCompletionCountingBound_of_targetCoefficientRowsetAverage
    (hcount :
      V13RealLinearUniformCausalTwoOrMoreTargetCoefficientRowsetAverageBound) :
    V13RealLinearUniformCausalTwoOrMoreCompletionCountingBound :=
  V13RealLinearUniformCausalTwoOrMoreCompletionCountingBound_of_targetCoefficientFiberAverage
    (V13RealLinearUniformCausalTwoOrMoreTargetCoefficientFiberAverageBound_of_rowsetAverage
      hcount)

theorem
    V13RealLinearUniformCausalTwoOrMoreTargetCoefficientRowsetProductAverageBound_of_rowsetAverage
    (hcount :
      V13RealLinearUniformCausalTwoOrMoreTargetCoefficientRowsetAverageBound) :
    V13RealLinearUniformCausalTwoOrMoreTargetCoefficientRowsetProductAverageBound := by
  intro m q observer i₀ hqgt hqm
  let E := v13RealLinearUniformCausalQRowExperiment observer
  let Q := 2 ^ q
  let S := Fintype.card (V13F2LinearEquiv m)
  have hsum :
      (∑ A : V13F2LinearEquiv m,
        ∑ rows : Finset (Fin m),
          Fintype.card
            (V13RealLinearAdaptiveQRowGeneratedTargetCoefficientRowsetCell
              E i₀ A rows)) ≤
      Q * S := by
    simpa [E, Q, S] using hcount observer i₀ hqgt hqm
  calc
    (∑ A : V13F2LinearEquiv m,
        ∑ rows : Finset (Fin m),
          Fintype.card
              (V13RealLinearAdaptiveQRowRowsetFiber E A rows) *
            Fintype.card
              (V13RealLinearRowsTargetCoefficient A rows i₀)) =
        ∑ A : V13F2LinearEquiv m,
          ∑ rows : Finset (Fin m),
            Fintype.card
              (V13RealLinearAdaptiveQRowGeneratedTargetCoefficientRowsetCell
                E i₀ A rows) := by
      apply Finset.sum_congr rfl
      intro A _
      apply Finset.sum_congr rfl
      intro rows _
      exact
        (v13RealLinearAdaptiveQRowGeneratedTargetCoefficientRowsetCell_card_eq_product
          E i₀ A rows).symm
    _ ≤ Q * S := hsum

theorem
    V13RealLinearUniformCausalTwoOrMoreTargetCoefficientRowsetAverageBound_of_productAverage
    (hcount :
      V13RealLinearUniformCausalTwoOrMoreTargetCoefficientRowsetProductAverageBound) :
    V13RealLinearUniformCausalTwoOrMoreTargetCoefficientRowsetAverageBound := by
  intro m q observer i₀ hqgt hqm
  let E := v13RealLinearUniformCausalQRowExperiment observer
  let Q := 2 ^ q
  let S := Fintype.card (V13F2LinearEquiv m)
  have hsum :
      (∑ A : V13F2LinearEquiv m,
        ∑ rows : Finset (Fin m),
          Fintype.card
              (V13RealLinearAdaptiveQRowRowsetFiber E A rows) *
            Fintype.card
              (V13RealLinearRowsTargetCoefficient A rows i₀)) ≤
      Q * S := by
    simpa [E, Q, S] using hcount observer i₀ hqgt hqm
  calc
    (∑ A : V13F2LinearEquiv m,
        ∑ rows : Finset (Fin m),
          Fintype.card
            (V13RealLinearAdaptiveQRowGeneratedTargetCoefficientRowsetCell
              E i₀ A rows)) =
        ∑ A : V13F2LinearEquiv m,
          ∑ rows : Finset (Fin m),
            Fintype.card
                (V13RealLinearAdaptiveQRowRowsetFiber E A rows) *
              Fintype.card
                (V13RealLinearRowsTargetCoefficient A rows i₀) := by
      apply Finset.sum_congr rfl
      intro A _
      apply Finset.sum_congr rfl
      intro rows _
      exact
        v13RealLinearAdaptiveQRowGeneratedTargetCoefficientRowsetCell_card_eq_product
          E i₀ A rows
    _ ≤ Q * S := hsum

theorem
    V13RealLinearUniformCausalTwoOrMoreTargetCoefficientRowsetAverageBound_iff_productAverage :
    V13RealLinearUniformCausalTwoOrMoreTargetCoefficientRowsetAverageBound ↔
      V13RealLinearUniformCausalTwoOrMoreTargetCoefficientRowsetProductAverageBound :=
  ⟨V13RealLinearUniformCausalTwoOrMoreTargetCoefficientRowsetProductAverageBound_of_rowsetAverage,
    V13RealLinearUniformCausalTwoOrMoreTargetCoefficientRowsetAverageBound_of_productAverage⟩

theorem
    V13RealLinearUniformCausalTwoOrMoreTargetCoefficientBudgetedRowsetProductAverageBound_of_productAverage
    (hcount :
      V13RealLinearUniformCausalTwoOrMoreTargetCoefficientRowsetProductAverageBound) :
    V13RealLinearUniformCausalTwoOrMoreTargetCoefficientBudgetedRowsetProductAverageBound := by
  intro m q observer i₀ hqgt hqm
  let E := v13RealLinearUniformCausalQRowExperiment observer
  let Q := 2 ^ q
  let S := Fintype.card (V13F2LinearEquiv m)
  have hsum :
      (∑ A : V13F2LinearEquiv m,
        ∑ rows : Finset (Fin m),
          Fintype.card
              (V13RealLinearAdaptiveQRowRowsetFiber E A rows) *
            Fintype.card
              (V13RealLinearRowsTargetCoefficient A rows i₀)) ≤
      Q * S := by
    simpa [E, Q, S] using hcount observer i₀ hqgt hqm
  calc
    (∑ A : V13F2LinearEquiv m,
        ∑ rows : V13RealLinearBudgetedRowset m q,
          Fintype.card
              (V13RealLinearAdaptiveQRowRowsetFiber E A rows.val) *
            Fintype.card
              (V13RealLinearRowsTargetCoefficient A rows.val i₀)) =
        ∑ A : V13F2LinearEquiv m,
          ∑ rows : Finset (Fin m),
            Fintype.card
                (V13RealLinearAdaptiveQRowRowsetFiber E A rows) *
              Fintype.card
                (V13RealLinearRowsTargetCoefficient A rows i₀) := by
      apply Finset.sum_congr rfl
      intro A _
      exact
        (v13RealLinearAdaptiveQRow_rowsetProduct_sum_eq_budgeted
          E i₀ A).symm
    _ ≤ Q * S := hsum

theorem
    V13RealLinearUniformCausalTwoOrMoreTargetCoefficientRowsetProductAverageBound_of_budgetedRowsetProductAverage
    (hcount :
      V13RealLinearUniformCausalTwoOrMoreTargetCoefficientBudgetedRowsetProductAverageBound) :
    V13RealLinearUniformCausalTwoOrMoreTargetCoefficientRowsetProductAverageBound := by
  intro m q observer i₀ hqgt hqm
  let E := v13RealLinearUniformCausalQRowExperiment observer
  let Q := 2 ^ q
  let S := Fintype.card (V13F2LinearEquiv m)
  have hsum :
      (∑ A : V13F2LinearEquiv m,
        ∑ rows : V13RealLinearBudgetedRowset m q,
          Fintype.card
              (V13RealLinearAdaptiveQRowRowsetFiber E A rows.val) *
            Fintype.card
              (V13RealLinearRowsTargetCoefficient A rows.val i₀)) ≤
      Q * S := by
    simpa [E, Q, S] using hcount observer i₀ hqgt hqm
  calc
    (∑ A : V13F2LinearEquiv m,
        ∑ rows : Finset (Fin m),
          Fintype.card
              (V13RealLinearAdaptiveQRowRowsetFiber E A rows) *
            Fintype.card
              (V13RealLinearRowsTargetCoefficient A rows i₀)) =
        ∑ A : V13F2LinearEquiv m,
          ∑ rows : V13RealLinearBudgetedRowset m q,
            Fintype.card
                (V13RealLinearAdaptiveQRowRowsetFiber E A rows.val) *
              Fintype.card
                (V13RealLinearRowsTargetCoefficient A rows.val i₀) := by
      apply Finset.sum_congr rfl
      intro A _
      exact
        v13RealLinearAdaptiveQRow_rowsetProduct_sum_eq_budgeted E i₀ A
    _ ≤ Q * S := hsum

theorem
    V13RealLinearUniformCausalTwoOrMoreTargetCoefficientRowsetProductAverageBound_iff_budgetedRowsetProductAverage :
    V13RealLinearUniformCausalTwoOrMoreTargetCoefficientRowsetProductAverageBound ↔
      V13RealLinearUniformCausalTwoOrMoreTargetCoefficientBudgetedRowsetProductAverageBound :=
  ⟨V13RealLinearUniformCausalTwoOrMoreTargetCoefficientBudgetedRowsetProductAverageBound_of_productAverage,
    V13RealLinearUniformCausalTwoOrMoreTargetCoefficientRowsetProductAverageBound_of_budgetedRowsetProductAverage⟩

theorem
    V13RealLinearUniformCausalTwoOrMoreCoefficientCompressionBound_of_targetCoefficientRowsetProductAverage
    (hcount :
      V13RealLinearUniformCausalTwoOrMoreTargetCoefficientRowsetProductAverageBound) :
    V13RealLinearUniformCausalTwoOrMoreCoefficientCompressionBound :=
  V13RealLinearUniformCausalTwoOrMoreCoefficientCompressionBound_of_targetCoefficientRowsetAverage
    (V13RealLinearUniformCausalTwoOrMoreTargetCoefficientRowsetAverageBound_of_productAverage
      hcount)

theorem
    V13RealLinearUniformCausalTwoOrMoreCompletionCountingBound_of_targetCoefficientRowsetProductAverage
    (hcount :
      V13RealLinearUniformCausalTwoOrMoreTargetCoefficientRowsetProductAverageBound) :
    V13RealLinearUniformCausalTwoOrMoreCompletionCountingBound :=
  V13RealLinearUniformCausalTwoOrMoreCompletionCountingBound_of_targetCoefficientRowsetAverage
    (V13RealLinearUniformCausalTwoOrMoreTargetCoefficientRowsetAverageBound_of_productAverage
      hcount)

theorem
    V13RealLinearUniformCausalTwoOrMoreCoefficientCompressionBound_of_targetCoefficientBudgetedRowsetProductAverage
    (hcount :
      V13RealLinearUniformCausalTwoOrMoreTargetCoefficientBudgetedRowsetProductAverageBound) :
    V13RealLinearUniformCausalTwoOrMoreCoefficientCompressionBound :=
  V13RealLinearUniformCausalTwoOrMoreCoefficientCompressionBound_of_targetCoefficientRowsetProductAverage
    (V13RealLinearUniformCausalTwoOrMoreTargetCoefficientRowsetProductAverageBound_of_budgetedRowsetProductAverage
      hcount)

theorem
    V13RealLinearUniformCausalTwoOrMoreCompletionCountingBound_of_targetCoefficientBudgetedRowsetProductAverage
    (hcount :
      V13RealLinearUniformCausalTwoOrMoreTargetCoefficientBudgetedRowsetProductAverageBound) :
    V13RealLinearUniformCausalTwoOrMoreCompletionCountingBound :=
  V13RealLinearUniformCausalTwoOrMoreCompletionCountingBound_of_targetCoefficientRowsetProductAverage
    (V13RealLinearUniformCausalTwoOrMoreTargetCoefficientRowsetProductAverageBound_of_budgetedRowsetProductAverage
      hcount)

theorem
    V13RealLinearUniformCausalTwoOrMoreCompletionCountingBound_of_fiberAverageCoefficient
    (hcount :
      V13RealLinearUniformCausalTwoOrMoreFiberAverageCoefficientBound) :
    V13RealLinearUniformCausalTwoOrMoreCompletionCountingBound :=
  V13RealLinearUniformCausalTwoOrMoreCompletionCountingBound_of_coefficientCompression
    (V13RealLinearUniformCausalTwoOrMoreCoefficientCompressionBound_of_fiberAverage
      hcount)

theorem v13RealLinear_uniform_causal_qrow_success_bound_of_lowPositiveSpanCounting
    (hcount : V13RealLinearUniformCausalLowPositiveRowSpanCountingBound)
    {m q : Nat} (observer : V13RealLinearCausalRowObserver m q)
    (i₀ : Fin m) :
    v13RealLinearUniformCausalQRowSuccess observer i₀ ≤
      (1 / 2 : Rat) + v13RealLinearQRowEpsilon q m := by
  by_cases hqzero : q = 0
  · subst q
    exact v13RealLinear_uniform_causal_zero_row_success_bound observer i₀
  · by_cases hmq : m ≤ q
    · exact
        v13RealLinear_uniform_causal_high_budget_success_bound
          observer i₀ hmq
    · have hqpos : 0 < q := Nat.pos_of_ne_zero hqzero
      have hqm : q < m := by omega
      exact
        v13RealLinear_uniform_causal_qrow_success_bound_of_spanCounting
          observer i₀ (hcount observer i₀ hqpos hqm)

theorem v13RealLinear_uniform_causal_qrow_success_bound_of_completionCounting
    (hcount :
      V13RealLinearUniformCausalLowPositiveCompletionCountingBound)
    {m q : Nat} (observer : V13RealLinearCausalRowObserver m q)
    (i₀ : Fin m) :
    v13RealLinearUniformCausalQRowSuccess observer i₀ ≤
      (1 / 2 : Rat) + v13RealLinearQRowEpsilon q m :=
  v13RealLinear_uniform_causal_qrow_success_bound_of_lowPositiveSpanCounting
    (v13RealLinearUniformCausalLowPositiveRowSpanCountingBound_of_completionCounting
      hcount)
    observer i₀

theorem v13RealLinear_uniform_causal_qrow_success_bound_of_coefficientCounting
    (hcount :
      V13RealLinearUniformCausalLowPositiveCoefficientCountingBound)
    {m q : Nat} (observer : V13RealLinearCausalRowObserver m q)
    (i₀ : Fin m) :
    v13RealLinearUniformCausalQRowSuccess observer i₀ ≤
      (1 / 2 : Rat) + v13RealLinearQRowEpsilon q m :=
  v13RealLinear_uniform_causal_qrow_success_bound_of_completionCounting
    (v13RealLinearUniformCausalLowPositiveCompletionCountingBound_of_coefficientCounting
      hcount)
    observer i₀

theorem
    v13RealLinear_uniform_causal_qrow_success_bound_of_twoOrMoreSpanCounting
    (hcount :
      ∀ {m q : Nat} (observer : V13RealLinearCausalRowObserver m q)
        (i₀ : Fin m),
        1 < q → q < m →
          V13RealLinearUniformCausalRowSpanCountingBound observer i₀)
    {m q : Nat} (observer : V13RealLinearCausalRowObserver m q)
    (i₀ : Fin m) :
    v13RealLinearUniformCausalQRowSuccess observer i₀ ≤
      (1 / 2 : Rat) + v13RealLinearQRowEpsilon q m :=
  v13RealLinear_uniform_causal_qrow_success_bound_of_lowPositiveSpanCounting
    (V13RealLinearUniformCausalLowPositiveRowSpanCountingBound_of_twoOrMore
      hcount)
    observer i₀

theorem
    v13RealLinear_uniform_causal_qrow_success_bound_of_twoOrMoreCompletionCounting
    (hcount :
      ∀ {m q : Nat} (observer : V13RealLinearCausalRowObserver m q)
        (i₀ : Fin m),
        1 < q → q < m →
          Fintype.card
              (V13RealLinearAdaptiveQRowGenerated
                (v13RealLinearUniformCausalQRowExperiment observer) i₀) *
            2 ^ m ≤
          2 ^ q *
            Fintype.card
              (V13RealLinearAdaptiveQRowWorld m (V13F2LinearEquiv m)))
    {m q : Nat} (observer : V13RealLinearCausalRowObserver m q)
    (i₀ : Fin m) :
    v13RealLinearUniformCausalQRowSuccess observer i₀ ≤
      (1 / 2 : Rat) + v13RealLinearQRowEpsilon q m :=
  v13RealLinear_uniform_causal_qrow_success_bound_of_completionCounting
    (V13RealLinearUniformCausalLowPositiveCompletionCountingBound_of_twoOrMore
      hcount)
    observer i₀

theorem
    v13RealLinear_uniform_causal_qrow_success_bound_of_twoOrMoreRowSpanCountingBound
    (hcount :
      V13RealLinearUniformCausalTwoOrMoreRowSpanCountingBound)
    {m q : Nat} (observer : V13RealLinearCausalRowObserver m q)
    (i₀ : Fin m) :
    v13RealLinearUniformCausalQRowSuccess observer i₀ ≤
      (1 / 2 : Rat) + v13RealLinearQRowEpsilon q m :=
  v13RealLinear_uniform_causal_qrow_success_bound_of_lowPositiveSpanCounting
    (V13RealLinearUniformCausalLowPositiveRowSpanCountingBound_of_twoOrMoreBound
      hcount)
    observer i₀

theorem
    v13RealLinear_uniform_causal_qrow_success_bound_of_twoOrMoreCompletionCountingBound
    (hcount :
      V13RealLinearUniformCausalTwoOrMoreCompletionCountingBound)
    {m q : Nat} (observer : V13RealLinearCausalRowObserver m q)
    (i₀ : Fin m) :
    v13RealLinearUniformCausalQRowSuccess observer i₀ ≤
      (1 / 2 : Rat) + v13RealLinearQRowEpsilon q m :=
  v13RealLinear_uniform_causal_qrow_success_bound_of_completionCounting
    (V13RealLinearUniformCausalLowPositiveCompletionCountingBound_of_twoOrMoreBound
      hcount)
    observer i₀

theorem
    v13RealLinear_uniform_causal_qrow_success_bound_of_twoOrMoreCoefficientCountingBound
    (hcount :
      V13RealLinearUniformCausalTwoOrMoreCoefficientCountingBound)
    {m q : Nat} (observer : V13RealLinearCausalRowObserver m q)
    (i₀ : Fin m) :
    v13RealLinearUniformCausalQRowSuccess observer i₀ ≤
      (1 / 2 : Rat) + v13RealLinearQRowEpsilon q m :=
  v13RealLinear_uniform_causal_qrow_success_bound_of_completionCounting
    (V13RealLinearUniformCausalLowPositiveCompletionCountingBound_of_twoOrMoreCoefficientCounting
      hcount)
    observer i₀

theorem
    v13RealLinear_uniform_causal_qrow_success_bound_of_twoOrMoreCoefficientCompressionBound
    (hcount :
      V13RealLinearUniformCausalTwoOrMoreCoefficientCompressionBound)
    {m q : Nat} (observer : V13RealLinearCausalRowObserver m q)
    (i₀ : Fin m) :
    v13RealLinearUniformCausalQRowSuccess observer i₀ ≤
      (1 / 2 : Rat) + v13RealLinearQRowEpsilon q m :=
  v13RealLinear_uniform_causal_qrow_success_bound_of_twoOrMoreCoefficientCountingBound
    (V13RealLinearUniformCausalTwoOrMoreCoefficientCountingBound_of_compression
      hcount)
    observer i₀

theorem
    v13RealLinear_uniform_causal_qrow_success_bound_of_twoOrMoreFiberAverageCoefficientBound
    (hcount :
      V13RealLinearUniformCausalTwoOrMoreFiberAverageCoefficientBound)
    {m q : Nat} (observer : V13RealLinearCausalRowObserver m q)
    (i₀ : Fin m) :
    v13RealLinearUniformCausalQRowSuccess observer i₀ ≤
      (1 / 2 : Rat) + v13RealLinearQRowEpsilon q m :=
  v13RealLinear_uniform_causal_qrow_success_bound_of_twoOrMoreCoefficientCompressionBound
    (V13RealLinearUniformCausalTwoOrMoreCoefficientCompressionBound_of_fiberAverage
      hcount)
    observer i₀

theorem
    v13RealLinear_uniform_causal_qrow_success_bound_of_twoOrMoreTargetCoefficientFiberAverageBound
    (hcount :
      V13RealLinearUniformCausalTwoOrMoreTargetCoefficientFiberAverageBound)
    {m q : Nat} (observer : V13RealLinearCausalRowObserver m q)
    (i₀ : Fin m) :
    v13RealLinearUniformCausalQRowSuccess observer i₀ ≤
      (1 / 2 : Rat) + v13RealLinearQRowEpsilon q m :=
  v13RealLinear_uniform_causal_qrow_success_bound_of_twoOrMoreFiberAverageCoefficientBound
    (V13RealLinearUniformCausalTwoOrMoreFiberAverageCoefficientBound_of_targetCoefficientFiberAverage
      hcount)
    observer i₀

theorem
    v13RealLinear_uniform_causal_qrow_success_bound_of_twoOrMoreTargetCoefficientRowsetAverageBound
    (hcount :
      V13RealLinearUniformCausalTwoOrMoreTargetCoefficientRowsetAverageBound)
    {m q : Nat} (observer : V13RealLinearCausalRowObserver m q)
    (i₀ : Fin m) :
    v13RealLinearUniformCausalQRowSuccess observer i₀ ≤
      (1 / 2 : Rat) + v13RealLinearQRowEpsilon q m :=
  v13RealLinear_uniform_causal_qrow_success_bound_of_twoOrMoreTargetCoefficientFiberAverageBound
    (V13RealLinearUniformCausalTwoOrMoreTargetCoefficientFiberAverageBound_of_rowsetAverage
      hcount)
    observer i₀

theorem
    v13RealLinear_uniform_causal_qrow_success_bound_of_twoOrMoreTargetCoefficientRowsetProductAverageBound
    (hcount :
      V13RealLinearUniformCausalTwoOrMoreTargetCoefficientRowsetProductAverageBound)
    {m q : Nat} (observer : V13RealLinearCausalRowObserver m q)
    (i₀ : Fin m) :
    v13RealLinearUniformCausalQRowSuccess observer i₀ ≤
      (1 / 2 : Rat) + v13RealLinearQRowEpsilon q m :=
  v13RealLinear_uniform_causal_qrow_success_bound_of_twoOrMoreTargetCoefficientRowsetAverageBound
    (V13RealLinearUniformCausalTwoOrMoreTargetCoefficientRowsetAverageBound_of_productAverage
      hcount)
    observer i₀

theorem
    v13RealLinear_uniform_causal_qrow_success_bound_of_twoOrMoreTargetCoefficientBudgetedRowsetProductAverageBound
    (hcount :
      V13RealLinearUniformCausalTwoOrMoreTargetCoefficientBudgetedRowsetProductAverageBound)
    {m q : Nat} (observer : V13RealLinearCausalRowObserver m q)
    (i₀ : Fin m) :
    v13RealLinearUniformCausalQRowSuccess observer i₀ ≤
      (1 / 2 : Rat) + v13RealLinearQRowEpsilon q m :=
  v13RealLinear_uniform_causal_qrow_success_bound_of_twoOrMoreTargetCoefficientRowsetProductAverageBound
    (V13RealLinearUniformCausalTwoOrMoreTargetCoefficientRowsetProductAverageBound_of_budgetedRowsetProductAverage
      hcount)
    observer i₀

theorem v13RealLinear_qrow_epsilon_nonnegative (q m : Nat) :
    0 ≤ v13RealLinearQRowEpsilon q m := by
  unfold v13RealLinearQRowEpsilon
  positivity

end Mettapedia.Computability.PNP
