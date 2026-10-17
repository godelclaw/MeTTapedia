import Foundation.FirstOrder.Incompleteness.Second
import Mettapedia.Logic.Diagonal.Provability

/-!
# Arithmetic as a provability stage: the diagonal lemma as the diagonal step

The provability stages of `Mettapedia.Logic.Diagonal.Provability` are instantiated by every
`Δ₁` theory of arithmetic extending `𝗜𝚺₁`, from the Foundation library: sentences of the
language of arithmetic, provability in the theory, the material conditional, falsum, and the
standard provability predicate as the internal operator.  The derivability conditions are
Foundation's (`D1`, `D2`, `D3`).

**Codes and the diagonal.**  Codes are formulas with one free variable, and the code map
applies a formula to the numeral of the Gödel number of a formula (`run`).  The formula
`diag θ` represents, provably in the theory, the composite `ψ ↦ θ(⌜ψ(⌜ψ⌝)⌝)`
(`diag_represents`): the arithmetic content of the diagonal lemma is exactly this
representation.  So the stage is diagonalizable along `run` (`stage_diagonalizable`), and its
Löb sentences come from the relative Lawvere step
`Mettapedia.Logic.Diagonal.exists_fixedPoint`.

**Consequences, through the abstract theorems.**  Löb's theorem (`loeb`) and the second
incompleteness theorem (`consistency_unprovable`) for every consistent `Δ₁` extension of
`𝗜𝚺₁`, derived from the diagonal step and the derivability conditions alone.  The
consistency statement of the abstract stage, `□⊥ → ⊥`, is provably equivalent to the
theory's own (`consistency_equivalent`), and the conclusion agrees with Foundation's
`consistent_unprovable` (control `agrees_with_foundation`).

**The stratified escape.**  A theory true in the standard model has that model as a model
one level up (`standardModel`), so it is consistent and does not prove its own consistency
(`stratified_of_sound`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.Diagonal.Arithmetic

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open LO.FirstOrder.ProvabilityAbstraction
open LO.FirstOrder.Arithmetic.Bootstrapping LO.FirstOrder.Arithmetic.Bootstrapping.Arithmetic

/-- **The arithmetic code map**: a formula with one free variable, applied to the numeral of
the Gödel number of a formula. -/
noncomputable def run (code argument : Semisentence ℒₒᵣ 1) : ArithmeticSentence :=
  code/[⌜argument⌝]

variable (T : ArithmeticTheory) [𝗜𝚺₁ ⪯ T]

/-- **The diagonal representation.**  `diag θ`, applied to the code of `ψ`, is provably
equivalent to `θ` applied to the code of `ψ(⌜ψ⌝)`. -/
theorem diag_represents (θ ψ : Semisentence ℒₒᵣ 1) :
    T ⊢ run (diag θ) ψ ⭤ θ/[⌜run ψ ψ⌝] :=
  haveI : 𝗘𝗤 ⪯ T := Entailment.WeakerThan.trans (𝓣 := 𝗜𝚺₁) inferInstance inferInstance
  provable_of_models _ _ fun (V : Type) _ _ ↦ by
    have : V ⊧ₘ* 𝗜𝚺₁ := ModelsTheory.of_provably_subtheory V 𝗜𝚺₁ T inferInstance
    suffices V ⊧/![] (run (diag θ) ψ) ↔ V ⊧/![⌜run ψ ψ⌝] θ by
      simpa [models_iff, Matrix.constant_eq_singleton]
    let t : V := ⌜ψ⌝
    have substituted : substNumeral t t = ⌜run ψ ψ⌝ := by
      simp [t, run, substNumeral_app_quote]
    calc
      V ⊧/![] (run (diag θ) ψ)
    _ ↔ V ⊧/![t] (diag θ) := by simp [run, Matrix.constant_eq_singleton, t]
    _ ↔ V ⊧/![substNumeral t t] θ := by simp [diag, Matrix.constant_eq_singleton]
    _ ↔ V ⊧/![⌜run ψ ψ⌝] θ := by simp [substituted]

variable [T.Δ₁]

/-- `𝗣𝗔⁻` is below every extension of `𝗜𝚺₁`; the third derivability condition uses it. -/
instance peanoMinus_le : 𝗣𝗔⁻ ⪯ T := Entailment.WeakerThan.trans (𝓣 := 𝗜𝚺₁) inferInstance inferInstance

/-- **The arithmetic provability stage of `T`**: provability in `T`, with the standard
provability predicate as the internal operator. -/
noncomputable def stage : ProvabilityStage ArithmeticSentence where
  Proves σ := T ⊢ σ
  imp σ π := σ ➝ π
  falsum := ⊥
  box σ := T.standardProvability σ
  modusPonens implication proved := implication ⨀ proved
  axiomK _ _ := implyK!
  axiomS _ _ _ := implyS!
  necessitation proved := D1_shift proved
  boxDistribution _ _ := D2_shift
  boxBox _ := D3_shift

/-- The formula `x ↦ (□x → c)`. -/
noncomputable def loebFormula (c : ArithmeticSentence) : Semisentence ℒₒᵣ 1 :=
  “x. !(T.standardProvability).prov x → !c”

omit [𝗜𝚺₁ ⪯ T] in
theorem loebFormula_subst (c σ : ArithmeticSentence) :
    (loebFormula T c)/[⌜σ⌝] = T.standardProvability σ ➝ c := by
  simp [loebFormula, Provability.pr, Rew.subst_comp_subst, ← TransitiveRewriting.comp_app]

/-- **The stage is diagonalizable along the code map**: `diag (loebFormula c)` represents
the diagonal composite of `x ↦ (□x → c)`. -/
theorem stage_diagonalizable : (stage T).Diagonalizable run := by
  intro c
  refine ⟨diag (loebFormula T c), fun ψ => ?_⟩
  have represents := diag_represents T (loebFormula T c) ψ
  rw [loebFormula_subst] at represents
  exact ⟨K!_left represents, K!_right represents⟩

/-- **Löb's theorem for arithmetic**, through the diagonal step. -/
theorem loeb {c : ArithmeticSentence} (reflection : T ⊢ T.standardProvability c ➝ c) :
    T ⊢ c :=
  ProvabilityStage.loeb (stage_diagonalizable T) reflection

theorem stage_consistent [Entailment.Consistent T] : (stage T).Consistent :=
  Entailment.consistent_iff_unprovable_bot.mp inferInstance

/-- **The second incompleteness theorem for arithmetic**, through the diagonal step: a
consistent `Δ₁` extension of `𝗜𝚺₁` does not prove `□⊥ → ⊥`. -/
theorem consistency_unprovable [Entailment.Consistent T] :
    T ⊬ (T.standardProvability ⊥ ➝ ⊥) :=
  ProvabilityStage.not_proves_consistency (stage_diagonalizable T) (stage_consistent T)

omit [𝗜𝚺₁ ⪯ T] in
/-- The stage's consistency statement is provably equivalent to the theory's. -/
theorem consistency_equivalent :
    T ⊢ (T.standardProvability ⊥ ➝ ⊥) ⭤ ↑T.consistent := by
  have negation : (↑T.consistent : ArithmeticSentence) = ∼T.standardProvability ⊥ := rfl
  rw [negation]
  cl_prover

/-- **Control.**  The conclusion agrees with Foundation's own second incompleteness theorem,
`consistent_unprovable`: both say that `T` does not prove its consistency statement. -/
theorem agrees_with_foundation [Entailment.Consistent T] :
    T ⊬ ↑T.consistent ∧ T ⊬ (T.standardProvability ⊥ ➝ ⊥) := by
  refine ⟨fun proved => consistency_unprovable T ?_, consistency_unprovable T⟩
  exact K!_right (consistency_equivalent T) ⨀ proved

/-- **The standard model, one level up**, for a theory true in it. -/
noncomputable def standardModel [ℕ ⊧ₘ* T] : ProvabilityStage.Model (stage T) where
  Holds σ := ℕ ⊧ₘ σ
  sound proved := models_of_provable inferInstance proved
  falsum_fails := by
    change ¬ ℕ ⊧ₘ (⊥ : ArithmeticSentence)
    simp

/-- **Stratification.**  A theory true in the standard model is consistent and does not prove
its own consistency statement: its consistency is seen one level up. -/
theorem stratified_of_sound [ℕ ⊧ₘ* T] :
    (stage T).Consistent ∧ ¬ (stage T).Proves (stage T).consistency :=
  ProvabilityStage.stratified (stage_diagonalizable T) (standardModel T)

#print axioms diag_represents
#print axioms stage_diagonalizable
#print axioms loeb
#print axioms consistency_unprovable
#print axioms agrees_with_foundation
#print axioms stratified_of_sound

end Mettapedia.Logic.Diagonal.Arithmetic
