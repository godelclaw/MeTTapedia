import Mettapedia.TypeTheory.BubbleWeakness
import Mettapedia.Logic.TheoryModel.WeakestCorrect
import Mathlib.Tactic.FinCases

/-!
# Choosing a bubble: Bennett's optimality over a catalog of strict models

A finite catalog of strict models stands for the interpretations a program or
a later program may rely on: the syntactic model, normal-form models, a cost
model, a proof-relevant model, the degenerate model.  A bubble's extension in
the catalog is the set of catalogued models it keeps (`catalogModels`); more
conversion keeps fewer of them (`catalogModels_anti`).

An observation records the interpretations already observed and those that must stay
models; a bubble is correct when it keeps exactly those among the observed ones.
For the interpretations not yet observed, the theorems of `WeakestCorrect` give
Bennett's optimality for bubble selection:

* under any exchangeable law of future requirements, survival is monotone in
  the number of catalogued models kept (`bubble_survival_mono`);
* among correct bubbles, one that converts everything another converts never
  survives better (`survival_antitone_in_conversion`).

Quantale weakness reads the same order: the weakness of the diagonal event of a
bubble's catalogued models, for any weighting in any quantale, is antitone in
conversion (`catalogQuantaleWeakness_anti`).  The structures weighed are the
models, not the expressions: the identifications a bubble makes between
expressions are commitments, and coarsening them removes models.

So among the bubbles correct for what has been observed, the one declaring the
least definitional equality is the one most likely to stay compatible with the
interpretations later programs require.

**Worked example** (`CatalogExample`): four interpretations of the arithmetic
core (syntactic, recursion normal form, left-unit normal form, degenerate); the
syntactic one has been observed and must be excluded, the degenerate one is
always kept.  For the program that uses a vector of length zero at length
`0 + 0`, the recursion bubble and the left-unit bubble are both correct and each
survives a uniform future with probability one half; the obligation bubble is
correct and survives with probability one.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.BubbleSelection

open Mettapedia.Logic.TheoryModel
open Mettapedia.Logic.TheoryModel.WeakestCorrect
open Mettapedia.TypeTheory.BubbleConversion
open Mettapedia.TypeTheory.BubbleWeakness
open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.Embedding.SimpleSliceOfDependent
open Mettapedia.Algebra.QuantaleWeakness
open Mettapedia.GSLT.Meredith.WeaknessBridge

universe u v uQ

variable {Base : Type u} {Const : Ty Base → Type v} {n : ℕ}

/-- A bubble, as a candidate: its declared rule set. -/
abbrev Bubble (Base : Type u) (Const : Ty Base → Type v) :=
  Expr Base Const → Expr Base Const → Prop

open Classical in
/-- The members of a finite catalog of strict models that are strict models of
a bubble. -/
noncomputable def catalogModels (catalog : Fin n → Congruence Base Const)
    (bubble : Bubble Base Const) : Finset (Fin n) :=
  Finset.univ.filter fun i => catalog i ∈ models strictSat (equations bubble)

theorem mem_catalogModels {catalog : Fin n → Congruence Base Const}
    {bubble : Bubble Base Const} {i : Fin n} :
    i ∈ catalogModels catalog bubble ↔ catalog i ∈ models strictSat (equations bubble) := by
  classical
  simp [catalogModels]

/-- More conversion keeps fewer catalogued models. -/
theorem catalogModels_anti {catalog : Fin n → Congruence Base Const}
    {small large : Bubble Base Const}
    (contained : ∀ e e' : Expr Base Const, Convertible small e e' → Convertible large e e') :
    catalogModels catalog large ⊆ catalogModels catalog small :=
  fun _ member =>
    mem_catalogModels.mpr (models_equations_subset_iff.mpr contained (mem_catalogModels.mp member))

/-- **Bennett's optimality for bubble selection**: among bubbles correct for the
observed interpretations, survival under an exchangeable future is monotone in
the number of catalogued strict models kept. -/
theorem bubble_survival_mono {catalog : Fin n → Congruence Base Const} {law : ℕ → ℚ}
    (nonneg : ∀ k, 0 ≤ law k) {obs : Observation (Fin n)} {left right : Bubble Base Const}
    (leftCorrect : Correct (catalogModels catalog) obs left)
    (rightCorrect : Correct (catalogModels catalog) obs right)
    (le : (catalogModels catalog left).card ≤ (catalogModels catalog right).card) :
    exchangeableSurvival (catalogModels catalog) law obs left ≤
      exchangeableSurvival (catalogModels catalog) law obs right :=
  exchangeableSurvival_mono nonneg leftCorrect rightCorrect le

/-- **More conversion never survives better** among correct bubbles. -/
theorem survival_antitone_in_conversion {catalog : Fin n → Congruence Base Const}
    {law : ℕ → ℚ} (nonneg : ∀ k, 0 ≤ law k) {obs : Observation (Fin n)}
    {small large : Bubble Base Const}
    (smallCorrect : Correct (catalogModels catalog) obs small)
    (largeCorrect : Correct (catalogModels catalog) obs large)
    (contained : ∀ e e' : Expr Base Const, Convertible small e e' → Convertible large e e') :
    exchangeableSurvival (catalogModels catalog) law obs large ≤
      exchangeableSurvival (catalogModels catalog) law obs small :=
  exchangeableSurvival_mono nonneg largeCorrect smallCorrect
    (Finset.card_le_card (catalogModels_anti contained))

/-- The quantale weakness of a bubble over the catalogue: the weakness of the
diagonal event of its catalogued strict models. -/
noncomputable def catalogQuantaleWeakness {Q : Type uQ} [Monoid Q] [CompleteLattice Q]
    (catalog : Fin n → Congruence Base Const) (ev : GSLTEvidence (Fin n) Q)
    (bubble : Bubble Base Const) : Q :=
  gsltWeakness ev (inducedDiagonalEvent (catalogModels catalog bubble))

/-- **Quantale weakness is antitone in conversion.** -/
theorem catalogQuantaleWeakness_anti {Q : Type uQ} [Monoid Q] [CompleteLattice Q]
    {catalog : Fin n → Congruence Base Const} (ev : GSLTEvidence (Fin n) Q)
    {small large : Bubble Base Const}
    (contained : ∀ e e' : Expr Base Const, Convertible small e e' → Convertible large e e') :
    catalogQuantaleWeakness catalog ev large ≤ catalogQuantaleWeakness catalog ev small :=
  weakness_mono _ _ _ (Finset.map_subset_map.mpr (catalogModels_anti contained))

/-! ## Worked example -/

namespace CatalogExample

open Mettapedia.TypeTheory.BubbleConversion.Arith
open Mettapedia.TypeTheory.BubbleWeakness.ArithControl
open Mettapedia.Enactive.GeneralizationOptimality
open Mettapedia.Logic.HOL.Embedding.SimpleSliceOfDependent.Expr

/-- Four interpretations of the arithmetic core: the syntactic model, the
recursion normal form, the left-unit normal form, and the degenerate model. -/
def catalog : Fin 4 → Congruence Unit ArithConst
  | 0 => syntactic
  | 1 => normModel false
  | 2 => leftModel
  | 3 => total

/-- Observed so far: the syntactic model, which must be excluded, and the
degenerate model, which every bubble keeps. -/
def observed : Observation (Fin 4) where
  seen := {0, 3}
  admitted := {3}
  admitted_subset := by decide

/-- The obligation bubble of the program using `Vec 0` at `Vec (0 + 0)`. -/
def obligation : Bubble Unit ArithConst :=
  obligations zeroVecProgram

theorem syntactic_not_rule : syntactic ∉ models strictSat (equations Rule) := by
  intro model
  have same := syntactic_mem_models_iff.mp model _ _
    (Relation.EqvGen.rel _ _ (Rewrite.root (Rule.addZero (bvar 0))))
  simp [addE, zeroE] at same

theorem syntactic_not_leftUnit : syntactic ∉ models strictSat (equations LeftUnit) := by
  intro model
  have same := syntactic_mem_models_iff.mp model _ _
    (Relation.EqvGen.rel _ _ (Rewrite.root (LeftUnit.zeroAdd (bvar 0))))
  simp [addE, zeroE] at same

theorem syntactic_not_obligation : syntactic ∉ models strictSat (equations obligation) := by
  intro model
  have same := syntactic_mem_models_iff.mp model (vec zeroE) (vec (addE zeroE zeroE))
    (Relation.EqvGen.rel _ _ (Rewrite.root ⟨_, rfl, zeroVec_typed, rfl⟩))
  simp [vec, addE, zeroE] at same

theorem normModel_not_leftUnit : normModel false ∉ models strictSat (equations LeftUnit) := by
  intro model
  have same := mem_models_equations.mp model _ _
    (Relation.EqvGen.rel _ _ (Rewrite.root (LeftUnit.zeroAdd (bvar 0))))
  simp [normModel, norm, appNorm, addNorm, addE, zeroE] at same

theorem leftModel_not_rule : leftModel ∉ models strictSat (equations Rule) := by
  intro model
  have same := mem_models_equations.mp model _ _
    (Relation.EqvGen.rel _ _ (Rewrite.root (Rule.addZero (bvar 0))))
  simp [leftModel, normLeft, appNormLeft, addE, zeroE] at same

theorem normModel_obligation : normModel false ∈ models strictSat (equations obligation) :=
  obligationBubble_weakest zeroVecProgram_typable arith_types_zeroVec normModel_mem

theorem leftModel_obligation : leftModel ∈ models strictSat (equations obligation) :=
  obligationBubble_weakest zeroVecProgram_typable leftUnit_types_zeroVec leftModel_mem

theorem catalogModels_rule : catalogModels catalog Rule = {1, 3} := by
  ext i
  rw [mem_catalogModels]
  fin_cases i
  · simpa [catalog] using syntactic_not_rule
  · simpa [catalog] using normModel_mem
  · simpa [catalog] using leftModel_not_rule
  · simpa [catalog] using total_mem_models Rule

theorem catalogModels_leftUnit : catalogModels catalog LeftUnit = {2, 3} := by
  ext i
  rw [mem_catalogModels]
  fin_cases i
  · simpa [catalog] using syntactic_not_leftUnit
  · simpa [catalog] using normModel_not_leftUnit
  · simpa [catalog] using leftModel_mem
  · simpa [catalog] using total_mem_models LeftUnit

theorem catalogModels_obligation : catalogModels catalog obligation = {1, 2, 3} := by
  ext i
  rw [mem_catalogModels]
  fin_cases i
  · simpa [catalog] using syntactic_not_obligation
  · simpa [catalog] using normModel_obligation
  · simpa [catalog] using leftModel_obligation
  · simpa [catalog] using total_mem_models obligation

theorem rule_correct : Correct (catalogModels catalog) observed Rule := by
  rw [Correct, catalogModels_rule]
  decide

theorem leftUnit_correct : Correct (catalogModels catalog) observed LeftUnit := by
  rw [Correct, catalogModels_leftUnit]
  decide

theorem obligation_correct : Correct (catalogModels catalog) observed obligation := by
  rw [Correct, catalogModels_obligation]
  decide

theorem unseen_card : (unseen observed).card = 2 := by
  decide

theorem rule_buffer_card : (buffer (catalogModels catalog) observed Rule).card = 1 := by
  rw [buffer, catalogModels_rule]
  decide

theorem leftUnit_buffer_card : (buffer (catalogModels catalog) observed LeftUnit).card = 1 := by
  rw [buffer, catalogModels_leftUnit]
  decide

theorem obligation_buffer_card :
    (buffer (catalogModels catalog) observed obligation).card = 2 := by
  rw [buffer, catalogModels_obligation]
  decide

/-- **The recursion bubble survives a uniform future with probability one
half.** -/
theorem rule_survival :
    (uniformFuture (catalogModels catalog) observed).probability Rule = 1 / 2 := by
  show (2 ^ (buffer (catalogModels catalog) observed Rule).card : ℚ) /
    (2 ^ (unseen observed).card : ℚ) = 1 / 2
  rw [rule_buffer_card, unseen_card]
  norm_num

/-- The left-unit bubble survives with probability one half. -/
theorem leftUnit_survival :
    (uniformFuture (catalogModels catalog) observed).probability LeftUnit = 1 / 2 := by
  show (2 ^ (buffer (catalogModels catalog) observed LeftUnit).card : ℚ) /
    (2 ^ (unseen observed).card : ℚ) = 1 / 2
  rw [leftUnit_buffer_card, unseen_card]
  norm_num

/-- **The obligation bubble survives every uniform future.** -/
theorem obligation_survival :
    (uniformFuture (catalogModels catalog) observed).probability obligation = 1 := by
  show (2 ^ (buffer (catalogModels catalog) observed obligation).card : ℚ) /
    (2 ^ (unseen observed).card : ℚ) = 1
  rw [obligation_buffer_card, unseen_card]
  norm_num

end CatalogExample

end Mettapedia.TypeTheory.BubbleSelection
