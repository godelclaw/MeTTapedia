import Mettapedia.Logic.Diagonal.InductionSchemeDelta1
import Mettapedia.Logic.Diagonal.Arithmetic
import Mettapedia.SetTheory.OpenTower.NoIsolatedCompletion

/-!
# The consistency tower: every stage certified by the next, none by itself

A **sound stage** is a `Δ₁` theory of arithmetic that extends `𝗜𝚺₁` and is true in the
standard model.  **Zoom-out** adds the stage's own consistency statement
(`SoundStage.next`), and the result is again a sound stage.  Iterating it gives the finite
levels of the progression of consistency extensions (`SoundStage.tower`).

* Each stage's consistency is proved at the next stage (`next_proves_consistency`) and not
  at the stage itself (`not_proves_own_consistency`), by the second incompleteness theorem
  in the form derived from the diagonal step
  (`Mettapedia.Logic.Diagonal.Arithmetic.agrees_with_foundation`).
* So zoom-out is strict (`strictlyWeaker_next`, `tower_strictMono`; and in the abstract
  form `ProvabilityStage.proves_beyond_of_proves_consistency`, `abstract_zoomOut`), and
  the sound stages under strict extension have no terminal stage (`noTerminalStage`, in the
  sense of `NoIsolatedCompletion.NoTerminalStage`).
* Zoom-out has no fixed point: no sound stage contains its zoom-out (`not_next_le`).
* Every zoom-out adds a new truth of the standard model (`next_new_truth`), and no stage
  proves every truth of it (`truth_not_reached`): the standard model is sound for every
  stage and is reached by none.  In Foundation's own terms, every stage is strictly weaker
  than true arithmetic (`strictlyWeaker_trueArith`).

**The tower from `𝗣𝗔`.**  `𝗣𝗔` and `𝗜𝚺₁` are sound stages (`peano`, `iSigmaOne`): their
`Δ₁` presentations are constructed, not postulated (`InductionSchemeDelta1.peanoDelta1`,
`InductionSchemeDelta1.iSigmaOneDelta1`), and Foundation proves that the standard model
satisfies both (`models_Peano`, `models_ISigmaOne`).  So the sound stages exist, and every statement above has content at
`𝗣𝗔, 𝗣𝗔 + Con(𝗣𝗔), …`: the levels increase strictly and are pairwise distinct
(`peano_tower_strictMono`, `peano_tower_injective`), no level is a top
(`peano_tower_no_top`), each level's consistency is proved one level up and not at the level
itself (`peano_tower_certified`, `peano_tower_not_self_certified`), and each level misses a
truth of the standard model (`peano_tower_true_unprovable`).

**Controls.**  Positive: `𝗣𝗔 + Con(𝗣𝗔)` proves `Con(𝗣𝗔)`
(`peano_next_proves_consistency`), and likewise for `𝗜𝚺₁`.  Negative: `𝗣𝗔` does not
(`peano_not_proves_consistency`), and likewise for `𝗜𝚺₁`.  Negative, for the definition:
the `Δ₁` field is what excludes a top.  True arithmetic satisfies every other field and
proves every truth, and it has no `Δ₁` presentation (`trueArith_not_delta1`).

**What is not claimed.**  Only the finite levels are built.  The transfinite progressions
along ordinal notations, where limit stages collect the earlier ones, need a uniform
arithmetic presentation of the stages and are not formalized here; nor is the completeness
of such progressions.  The consistency statement depends on the chosen `Δ₁` presentation,
and the tower is the tower of these presentations.

**Set stages.**  `ZFCStages.zfc_consistent_of_stage` proves the consistency of `𝗭𝗙𝗖` from
a set model one stage up: that is the stratified escape (`ProvabilityStage.Model.consistent`)
seen by the host.  Here the certification is internal to the next stage, as an axiom true in
the standard model.

**Checking without detaching.**  A stage proves, of every theorem of its zoom-out, that the
zoom-out proves it (`checks_next`): a weaker checker verifies the stronger theory's
derivations.  It cannot pass from that verification to the theorem itself: local reflection
of the zoom-out at `Con` of the stage is unprovable in the stage
(`not_detaches_next_consistency`; at `𝗣𝗔`, `peano_not_detaches_next_consistency`).  The
standard model, one level up, validates every such reflection statement
(`standardModel_detaches_next`).
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.OpenTower.ConsistencyTower

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open Mettapedia.Logic.Diagonal
open Mettapedia.SetTheory.OpenTower.NoIsolatedCompletion (NoTerminalStage)

/-- **A sound stage**: a `Δ₁` theory of arithmetic, extending `𝗜𝚺₁`, true in the standard
model. -/
structure SoundStage where
  theory : ArithmeticTheory
  [delta : theory.Δ₁]
  [extendsBase : 𝗜𝚺₁ ⪯ theory]
  [sound : ℕ ⊧ₘ* theory]

attribute [instance] SoundStage.delta SoundStage.extendsBase SoundStage.sound

namespace SoundStage

variable (S : SoundStage)

/-- A sound stage is consistent: the standard model is a model one level up. -/
instance consistent : Entailment.Consistent S.theory :=
  Entailment.consistent_iff_unprovable_bot.mpr (Arithmetic.standardModel S.theory).consistent

/-- **Zoom-out**: add the stage's own consistency statement. -/
noncomputable def next : SoundStage where
  theory := S.theory + S.theory.Con
  extendsBase := Entailment.WeakerThan.trans (𝓣 := S.theory) inferInstance inferInstance

theorem next_theory : S.next.theory = S.theory + S.theory.Con := rfl

/-- A stage is contained in its zoom-out. -/
instance le_next : S.theory ⪯ S.next.theory :=
  show S.theory ⪯ S.theory + S.theory.Con from inferInstance

/-- **Each stage's consistency is proved at the next stage.** -/
theorem next_proves_consistency : S.next.theory ⊢ ↑S.theory.consistent :=
  Entailment.by_axm _ (by simp [next_theory, Theory.add_def])

/-- **No stage proves its own consistency.** -/
theorem not_proves_own_consistency : S.theory ⊬ ↑S.theory.consistent :=
  (Arithmetic.agrees_with_foundation S.theory).1

/-- **Zoom-out is strict.** -/
theorem strictlyWeaker_next : S.theory ⪱ S.next.theory :=
  StrictlyWeakerThan.of_unprovable_provable S.not_proves_own_consistency
    S.next_proves_consistency

/-- **Zoom-out has no fixed point**: no sound stage contains its zoom-out. -/
theorem not_next_le : ¬ S.next.theory ⪯ S.theory :=
  fun le => S.not_proves_own_consistency
    (Entailment.WeakerThan.pbl (h := le) S.next_proves_consistency)

/-- The consistency statement of a sound stage is true in the standard model. -/
theorem consistency_true : ℕ ⊧ₘ (↑S.theory.consistent : ArithmeticSentence) :=
  models_of_provable inferInstance S.next_proves_consistency

/-- **Every zoom-out adds a new truth** of the standard model. -/
theorem next_new_truth :
    ∃ σ : ArithmeticSentence, ℕ ⊧ₘ σ ∧ S.theory ⊬ σ ∧ S.next.theory ⊢ σ :=
  ⟨↑S.theory.consistent, S.consistency_true, S.not_proves_own_consistency,
    S.next_proves_consistency⟩

/-- **Every stage is strictly weaker than true arithmetic**: Foundation's form of
`truth_not_reached`, through the first incompleteness theorem. -/
theorem strictlyWeaker_trueArith : S.theory ⪱ 𝗧𝗔 := by
  have : 𝗥₀ ⪯ S.theory := Entailment.WeakerThan.trans (𝓣 := 𝗜𝚺₁) inferInstance inferInstance
  infer_instance

/-- **The abstract form of strict zoom-out**: the provability stage of the next theory proves
the consistency statement `□⊥ → ⊥` of the provability stage of this one, so it proves a
sentence this one does not. -/
theorem abstract_zoomOut :
    ∃ σ, (Arithmetic.stage S.next.theory).Proves σ ∧ ¬ (Arithmetic.stage S.theory).Proves σ := by
  refine ProvabilityStage.proves_beyond_of_proves_consistency
    (Arithmetic.stage_diagonalizable S.theory).hasLoebSentences
    (Arithmetic.stage_consistent S.theory) ?_
  change S.next.theory ⊢ S.theory.standardProvability ⊥ ➝ ⊥
  have equivalent :
      S.next.theory ⊢ (S.theory.standardProvability ⊥ ➝ ⊥) ⭤ ↑S.theory.consistent :=
    Entailment.WeakerThan.pbl (Arithmetic.consistency_equivalent S.theory)
  exact K!_right equivalent ⨀ S.next_proves_consistency

/-! ### Checking without detaching -/

/-- **A stage verifies its zoom-out's theorems**: whatever the next stage proves, this stage
proves that the next stage proves it. -/
theorem checks_next {σ : ArithmeticSentence} (proved : S.next.theory ⊢ σ) :
    S.theory ⊢ S.next.theory.standardProvability σ :=
  Entailment.WeakerThan.pbl (ProvabilityAbstraction.D1 (𝔅 := S.next.theory.standardProvability) proved)

/-- **A stage cannot detach what it verifies.**  The stage proves that the next stage proves
its consistency, and does not prove local reflection of the next stage at that sentence:
detaching would prove its own consistency. -/
theorem not_detaches_next_consistency :
    S.theory ⊬ (S.next.theory.standardProvability ↑S.theory.consistent ➝ ↑S.theory.consistent) :=
  fun detach => S.not_proves_own_consistency (detach ⨀ S.checks_next S.next_proves_consistency)

/-- **The standard model detaches.**  One level up, every local reflection statement of the
next stage is true. -/
theorem standardModel_detaches_next (σ : ArithmeticSentence) :
    ℕ ⊧ₘ (S.next.theory.standardProvability σ ➝ σ) :=
  (Arithmetic.standardReflectiveModel S.next.theory).holds_localReflection σ

/-- **The tower**: the finite levels of the progression of consistency extensions. -/
noncomputable def tower : ℕ → SoundStage
  | 0 => S
  | n + 1 => (tower n).next

theorem tower_succ (n : ℕ) : S.tower (n + 1) = (S.tower n).next := rfl

/-- Every stage of the tower proves the consistency of the stage below. -/
theorem tower_succ_proves_consistency (n : ℕ) :
    (S.tower (n + 1)).theory ⊢ ↑(S.tower n).theory.consistent :=
  (S.tower n).next_proves_consistency

/-- **The tower increases strictly.** -/
theorem tower_strictMono {m n : ℕ} (lt : m < n) : (S.tower m).theory ⪱ (S.tower n).theory := by
  induction n with
  | zero => exact absurd lt (Nat.not_lt_zero m)
  | succ n ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.mp lt with below | same
      · exact StrictlyWeakerThan.trans (ih below) (S.tower n).strictlyWeaker_next
      · subst same
        exact (S.tower m).strictlyWeaker_next

/-- **The levels of the tower are pairwise distinct.** -/
theorem tower_injective : Function.Injective fun n => (S.tower n).theory := by
  intro m n same
  replace same : (S.tower m).theory = (S.tower n).theory := same
  by_contra different
  rcases Nat.lt_or_gt_of_ne different with lt | gt
  · have below := (S.tower_strictMono lt).notWT
    rw [same] at below
    exact below (Entailment.WeakerThan.refl _)
  · have below := (S.tower_strictMono gt).notWT
    rw [same] at below
    exact below (Entailment.WeakerThan.refl _)

/-- **No level of the tower is a top.** -/
theorem tower_no_top : ¬ ∃ n, ∀ m, (S.tower m).theory ⪯ (S.tower n).theory :=
  fun ⟨n, top⟩ => (S.tower_strictMono (Nat.lt_succ_self n)).notWT (top (n + 1))

end SoundStage

/-- **No top, only zoom-out**: under strict extension, the sound stages have no terminal
stage. -/
theorem noTerminalStage :
    NoTerminalStage (fun S S' : SoundStage => S.theory ⪱ S'.theory) :=
  fun S => ⟨S.next, S.strictlyWeaker_next⟩

/-- **The standard model is never reached**: no sound stage proves every truth of the
standard model. -/
theorem truth_not_reached :
    ¬ ∃ S : SoundStage, ∀ σ : ArithmeticSentence, ℕ ⊧ₘ σ → S.theory ⊢ σ :=
  fun ⟨S, complete⟩ => S.not_proves_own_consistency (complete _ S.consistency_true)

/-! ## The tower from `𝗣𝗔` -/

/-- **`𝗣𝗔` as a sound stage**: `Δ₁` by the constructed presentation
`InductionSchemeDelta1.peanoDelta1`, above `𝗜𝚺₁`, and true in the standard model by
`models_Peano`. -/
noncomputable def peano : SoundStage where
  theory := 𝗣𝗔
  delta := InductionSchemeDelta1.peanoDelta1

/-- **`𝗜𝚺₁` as a sound stage**: `Δ₁` by the constructed presentation
`InductionSchemeDelta1.iSigmaOneDelta1`, and true in the standard model by
`models_ISigmaOne`. -/
noncomputable def iSigmaOne : SoundStage where
  theory := 𝗜𝚺₁
  delta := InductionSchemeDelta1.iSigmaOneDelta1

/-- The sound stages exist, so `noTerminalStage` and `truth_not_reached` are not vacuous. -/
instance : Nonempty SoundStage := ⟨peano⟩

theorem peano_tower_zero : (peano.tower 0).theory = 𝗣𝗔 := rfl

theorem peano_tower_one : (peano.tower 1).theory = 𝗣𝗔 + 𝗣𝗔.Con := rfl

/-- **The tower from `𝗣𝗔` increases strictly.** -/
theorem peano_tower_strictMono {m n : ℕ} (lt : m < n) :
    (peano.tower m).theory ⪱ (peano.tower n).theory :=
  peano.tower_strictMono lt

/-- **The levels of the tower from `𝗣𝗔` are pairwise distinct.** -/
theorem peano_tower_injective : Function.Injective fun n => (peano.tower n).theory :=
  peano.tower_injective

/-- **The tower from `𝗣𝗔` has no top.** -/
theorem peano_tower_no_top : ¬ ∃ n, ∀ m, (peano.tower m).theory ⪯ (peano.tower n).theory :=
  peano.tower_no_top

/-- **Each level of the tower from `𝗣𝗔` is certified one level up.** -/
theorem peano_tower_certified (n : ℕ) :
    (peano.tower (n + 1)).theory ⊢ ↑(peano.tower n).theory.consistent :=
  peano.tower_succ_proves_consistency n

/-- **No level of the tower from `𝗣𝗔` certifies itself.** -/
theorem peano_tower_not_self_certified (n : ℕ) :
    (peano.tower n).theory ⊬ ↑(peano.tower n).theory.consistent :=
  (peano.tower n).not_proves_own_consistency

/-- **Every level of the tower from `𝗣𝗔` misses a truth of the standard model.** -/
theorem peano_tower_true_unprovable (n : ℕ) :
    ∃ σ : ArithmeticSentence, ℕ ⊧ₘ σ ∧ (peano.tower n).theory ⊬ σ :=
  ⟨_, (peano.tower n).consistency_true, (peano.tower n).not_proves_own_consistency⟩

/-- **`𝗣𝗔` verifies that `𝗣𝗔 + Con(𝗣𝗔)` proves `Con(𝗣𝗔)`.** -/
theorem peano_checks_next_consistency :
    𝗣𝗔 ⊢ peano.next.theory.standardProvability ↑𝗣𝗔.consistent :=
  peano.checks_next peano.next_proves_consistency

/-- **`𝗣𝗔` cannot detach `Con(𝗣𝗔)` from that verification.** -/
theorem peano_not_detaches_next_consistency :
    𝗣𝗔 ⊬ (peano.next.theory.standardProvability ↑𝗣𝗔.consistent ➝ ↑𝗣𝗔.consistent) :=
  peano.not_detaches_next_consistency

/-! ### Controls -/

/-- Positive control: `𝗣𝗔 + Con(𝗣𝗔)` proves `Con(𝗣𝗔)`. -/
theorem peano_next_proves_consistency : 𝗣𝗔 + 𝗣𝗔.Con ⊢ ↑𝗣𝗔.consistent :=
  peano.next_proves_consistency

/-- Negative control: `𝗣𝗔` does not prove `Con(𝗣𝗔)`. -/
theorem peano_not_proves_consistency : 𝗣𝗔 ⊬ ↑𝗣𝗔.consistent :=
  peano.not_proves_own_consistency

/-- Positive control: `𝗜𝚺₁ + Con(𝗜𝚺₁)` proves `Con(𝗜𝚺₁)`. -/
theorem iSigmaOne_next_proves_consistency : 𝗜𝚺₁ + 𝗜𝚺₁.Con ⊢ ↑𝗜𝚺₁.consistent :=
  iSigmaOne.next_proves_consistency

/-- Negative control: `𝗜𝚺₁` does not prove `Con(𝗜𝚺₁)`. -/
theorem iSigmaOne_not_proves_consistency : 𝗜𝚺₁ ⊬ ↑𝗜𝚺₁.consistent :=
  iSigmaOne.not_proves_own_consistency

/-- **Negative control for the definition: without `Δ₁` there is a top.**  True arithmetic
extends `𝗜𝚺₁`, is true in the standard model and proves every truth of it, so it satisfies
every field of `SoundStage` except `Δ₁`; it has no `Δ₁` presentation. -/
theorem trueArith_not_delta1 : IsEmpty 𝗧𝗔.Δ₁ :=
  ⟨fun _ => by
    obtain ⟨σ, true, unprovable⟩ := exists_true_but_unprovable_sentence 𝗧𝗔
    exact unprovable (TA.provable_iff.mpr true)⟩

/-- The positive half of the same control: true arithmetic proves every truth. -/
theorem trueArith_proves_truths (σ : ArithmeticSentence) (true : ℕ ⊧ₘ σ) : 𝗧𝗔 ⊢ σ :=
  TA.provable_iff.mpr true

#print axioms SoundStage.next_proves_consistency
#print axioms SoundStage.not_proves_own_consistency
#print axioms SoundStage.strictlyWeaker_next
#print axioms SoundStage.not_next_le
#print axioms SoundStage.next_new_truth
#print axioms SoundStage.strictlyWeaker_trueArith
#print axioms SoundStage.abstract_zoomOut
#print axioms SoundStage.tower_strictMono
#print axioms SoundStage.tower_injective
#print axioms SoundStage.tower_no_top
#print axioms noTerminalStage
#print axioms truth_not_reached
#print axioms peano
#print axioms iSigmaOne
#print axioms peano_tower_strictMono
#print axioms peano_tower_injective
#print axioms peano_tower_no_top
#print axioms peano_tower_certified
#print axioms peano_tower_not_self_certified
#print axioms peano_tower_true_unprovable
#print axioms peano_next_proves_consistency
#print axioms peano_not_proves_consistency
#print axioms iSigmaOne_next_proves_consistency
#print axioms iSigmaOne_not_proves_consistency
#print axioms trueArith_not_delta1
#print axioms trueArith_proves_truths
#print axioms SoundStage.checks_next
#print axioms SoundStage.not_detaches_next_consistency
#print axioms SoundStage.standardModel_detaches_next
#print axioms peano_checks_next_consistency
#print axioms peano_not_detaches_next_consistency

end Mettapedia.SetTheory.OpenTower.ConsistencyTower
