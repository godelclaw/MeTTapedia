import Mettapedia.SetTheory.OpenTower.NoIsolatedCompletion
import Mettapedia.SetTheory.OpenTower.Stability
import Mettapedia.GSLT.Core.NonFactorization

/-!
# What one completion decides and the family of completions leaves open

A completion of a theory is a point of the Stone space of its Lindenbaum algebra. A point
*affirms* an element of a Boolean algebra when it lies in the clopen set that represents the
element (`Affirms`).

**One point decides, the family does not.**
* A point affirms the complement of an element exactly when it does not affirm the element
  (`affirms_compl_iff`), so one completion gives every sentence one verdict
  (`affirms_neg_iff`).
* What every point affirms is the top element (`forall_affirms_iff`): the sentences affirmed by
  every completion are exactly the theorems of the theory (`forall_affirms_iff_provable`).
* A sentence that the theory neither proves nor refutes is affirmed by one completion and
  refuted by another (`exists_disagreeing_of_independent`). For a consistent `Δ₁` extension of
  `𝗜𝚺₁` such a sentence exists, by the Gödel–Rosser theorem of the Foundation library
  (`arithmetic_completions_disagree`).
* One completion forgets which sentences are open: when some sentence is independent, the
  class of a sentence in the Lindenbaum algebra is not a function of the verdict of one
  completion (`class_not_factors_through_verdict`).
* The points are the two-valued readings: a point holds the top true and respects meets and
  complements (`affirms_top`, `affirms_inf_iff`, `affirms_compl_iff`), and every reading that
  does so is the reading of a point (`exists_point_of_reading`). The truth value of a sentence
  in a model of a first-order theory is a function of the class of the sentence
  (`models_iff_of_equivalent`, `model_verdict_factors_through_class`), so a model is one of the
  completions of the theory (`exists_completion_of_model`); when some sentence is independent,
  the class is not a function of the truth value (`class_not_factors_through_model_verdict`).
* Two structures that disagree on a sentence leave it open in their common theory
  (`common_theory_independent`). The first two stages of the tower of least closed sets over
  `∅` disagree on the axiom of infinity, so their common theory neither proves nor refutes it
  (`stage_theories_leave_infinity_open`), while each of the two stages decides it. For the
  same reason no closed set that has the first stage as a member is elementarily equivalent to
  it (`stage_zero_not_elementaryEquiv`): the first stage is maximal for elementary extension
  among the stages, though every stage is a member of a later one.

**Over a complete theory the completion is reached by one sentence.** If the theory already
decides every sentence, its Lindenbaum algebra has two values at most
(`eq_top_or_eq_bot_of_complete`), its space of completions has one point at most
(`subsingleton_stoneSpace_of_complete`), and that point is isolated
(`isOpen_singleton_of_complete`). The first-order theory of a structure is complete and
consistent (`structure_theory_complete`, `structure_theory_consistent`), so the theory of a set
model has exactly this shape (`structureTheory_completion_isolated`,
`structureTheory_completions_nonempty`). The refutation of an isolated completion
(`NoIsolatedCompletion.no_isolated_completion`) is therefore a statement about effectively
axiomatized theories, not about every base.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.OpenTower.Strength.Completions

open LO LO.FirstOrder LO.Entailment LO.FirstOrder.SetTheory
open Mettapedia.Foundations.Gunk
open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.Logic.HOL.Embedding ZFSetUniverseClosure
open InternalTower ExternalTower ZFCStages Stability
open TopologicalSpace

universe u v

/-! ## Points of a Stone space and what they affirm -/

section Stone

variable {B : Type u} [BooleanAlgebra B]

/-- A point of the Stone space of a Boolean algebra affirms an element when it lies in the
clopen set that represents the element. -/
def Affirms (x : StoneSpace B) (a : B) : Prop :=
  x ∈ (stoneRepr B a : Set (StoneSpace B))

/-- Every point affirms the top element. -/
theorem affirms_top (x : StoneSpace B) : Affirms x (⊤ : B) := by
  unfold Affirms
  rw [OrderIso.map_top]
  exact Set.mem_univ x

/-- No point affirms the bottom element. -/
theorem not_affirms_bot (x : StoneSpace B) : ¬ Affirms x (⊥ : B) := by
  unfold Affirms
  rw [OrderIso.map_bot]
  exact Set.notMem_empty x

/-- A point affirms what lies above something it affirms. -/
theorem Affirms.mono {x : StoneSpace B} {a b : B} (below : a ≤ b) (affirmed : Affirms x a) :
    Affirms x b :=
  (stoneRepr B).monotone below affirmed

/-- **One point decides.** A point affirms the complement of an element exactly when it does
not affirm the element. -/
theorem affirms_compl_iff (x : StoneSpace B) (a : B) : Affirms x aᶜ ↔ ¬ Affirms x a := by
  unfold Affirms
  have image : stoneRepr B aᶜ = (stoneRepr B a)ᶜ :=
    ((stoneRepr B).isCompl isCompl_compl).compl_eq.symm
  rw [image, Clopens.coe_compl]
  exact Iff.rfl

/-- A point affirms a meet exactly when it affirms both elements. -/
theorem affirms_inf_iff (x : StoneSpace B) (a b : B) :
    Affirms x (a ⊓ b) ↔ Affirms x a ∧ Affirms x b := by
  unfold Affirms
  rw [OrderIso.map_inf, Clopens.coe_inf]
  exact Set.mem_inter_iff x _ _

/-- What every point affirms is the top element. -/
theorem forall_affirms_iff (a : B) : (∀ x : StoneSpace B, Affirms x a) ↔ a = ⊤ := by
  constructor
  · intro all
    apply (stoneRepr B).injective
    rw [OrderIso.map_top]
    exact SetLike.coe_injective (Set.eq_univ_of_forall all)
  · rintro rfl x
    exact affirms_top x

/-- What some point affirms is anything but the bottom element. -/
theorem exists_affirms_iff (a : B) : (∃ x : StoneSpace B, Affirms x a) ↔ a ≠ ⊥ := by
  constructor
  · rintro ⟨x, affirmed⟩ rfl
    exact not_affirms_bot x affirmed
  · intro nonzero
    by_contra none
    apply nonzero
    apply (stoneRepr B).injective
    rw [OrderIso.map_bot]
    apply SetLike.coe_injective
    rw [Clopens.coe_bot]
    exact Set.eq_empty_of_forall_notMem fun x affirmed => none ⟨x, affirmed⟩

/-- **A two-valued reading is a point.** For every reading of the elements of a Boolean algebra
as true or false that holds the top element true and respects meets and complements, some
point affirms exactly what the reading holds true. -/
theorem exists_point_of_reading (v : B → Prop) (top : v ⊤)
    (inf : ∀ a b, v (a ⊓ b) ↔ v a ∧ v b) (compl : ∀ a, v aᶜ ↔ ¬ v a) :
    ∃ x : StoneSpace B, ∀ a, Affirms x a ↔ v a := by
  have mono : ∀ {a b : B}, a ≤ b → v a → v b := by
    intro a b below holds
    rw [← inf_eq_left.mpr below] at holds
    exact ((inf a b).mp holds).2
  have bot : ¬ v ⊥ := by
    intro holds
    rw [← compl_top] at holds
    exact (compl ⊤).mp holds top
  have sup : ∀ a b, v (a ⊔ b) → v a ∨ v b := by
    intro a b holds
    by_contra neither
    rw [not_or] at neither
    have both : v (aᶜ ⊓ bᶜ) := (inf _ _).mpr ⟨(compl a).mpr neither.1, (compl b).mpr neither.2⟩
    rw [← compl_sup] at both
    exact (compl _).mp both holds
  let falsified : Ideal (AsBoolRing B) :=
    { carrier := {f | ¬ v (ofBoolRing f)}
      zero_mem' := by simpa using bot
      add_mem' := by
        intro f g hf hg holds
        rw [ofBoolRing_add] at holds
        rcases sup _ _ (mono symmDiff_le_sup holds) with h | h
        · exact hf h
        · exact hg h
      smul_mem' := by
        intro c f hf holds
        rw [smul_eq_mul, ofBoolRing_mul] at holds
        exact hf ((inf _ _).mp holds).2 }
  have prime : falsified.IsPrime := by
    refine ⟨?_, ?_⟩
    · intro whole
      have one : (1 : AsBoolRing B) ∈ falsified := by rw [whole]; trivial
      exact one (by simpa using top)
    · intro f g product
      by_contra neither
      rw [not_or] at neither
      apply product
      rw [ofBoolRing_mul]
      exact (inf _ _).mpr ⟨not_not.mp neither.1, not_not.mp neither.2⟩
  refine ⟨⟨falsified, prime⟩, fun a => ?_⟩
  unfold Affirms
  rw [coe_stoneRepr]
  refine (PrimeSpectrum.mem_basicOpen _ _).trans ?_
  show ¬ ¬ v (ofBoolRing (toBoolRing a)) ↔ v a
  rw [ofBoolRing_toBoolRing, not_not]

end Stone

/-! ## Completions of a theory -/

section Systems

variable {F S : Type*} [DecidableEq F] [LogicalConnective F] [Entailment S F]
  (𝓢 : S) [Entailment.Cl 𝓢]

/-- **The sentences affirmed by every completion are the theorems.** -/
theorem forall_affirms_iff_provable (φ : F) :
    (∀ x : StoneSpace (LindenbaumAlgebra 𝓢), Affirms x (⟦φ⟧ : LindenbaumAlgebra 𝓢)) ↔ 𝓢 ⊢ φ := by
  rw [forall_affirms_iff, LindenbaumAlgebra.provable_iff_eq_top]

/-- **One completion gives every sentence one verdict**: it affirms the negation exactly when
it does not affirm the sentence. -/
theorem affirms_neg_iff (x : StoneSpace (LindenbaumAlgebra 𝓢)) (φ : F) :
    Affirms x (⟦∼φ⟧ : LindenbaumAlgebra 𝓢) ↔ ¬ Affirms x (⟦φ⟧ : LindenbaumAlgebra 𝓢) := by
  rw [← LindenbaumAlgebra.compl_def, affirms_compl_iff]

/-- **The family of completions leaves an independent sentence open**: one completion affirms
it and another affirms its negation. -/
theorem exists_disagreeing_of_independent {σ : F} (independent : Independent 𝓢 σ) :
    ∃ x y : StoneSpace (LindenbaumAlgebra 𝓢),
      Affirms x (⟦σ⟧ : LindenbaumAlgebra 𝓢) ∧ Affirms y (⟦∼σ⟧ : LindenbaumAlgebra 𝓢) := by
  have left : (⟦σ⟧ : LindenbaumAlgebra 𝓢) ≠ ⊥ := by
    intro zero
    apply independent.2
    rw [LindenbaumAlgebra.provable_iff_eq_top, ← LindenbaumAlgebra.compl_def, zero, compl_bot]
  have right : (⟦∼σ⟧ : LindenbaumAlgebra 𝓢) ≠ ⊥ := by
    intro zero
    apply independent.1
    rw [LindenbaumAlgebra.provable_iff_eq_top]
    rw [← LindenbaumAlgebra.compl_def, compl_eq_bot] at zero
    exact zero
  obtain ⟨x, hx⟩ := (exists_affirms_iff _).mpr left
  obtain ⟨y, hy⟩ := (exists_affirms_iff _).mpr right
  exact ⟨x, y, hx, hy⟩

/-- **One completion forgets which sentences are open.** When some sentence is independent, the
class of a sentence in the Lindenbaum algebra is not a function of the verdict one completion
gives it: a sentence that the completion affirms and the theory does not prove has the verdict
of a theorem and another class. -/
theorem class_not_factors_through_verdict {σ : F} (independent : Independent 𝓢 σ)
    (x : StoneSpace (LindenbaumAlgebra 𝓢)) :
    ¬ Factors (fun φ : F => Affirms x (⟦φ⟧ : LindenbaumAlgebra 𝓢))
      (fun φ : F => (⟦φ⟧ : LindenbaumAlgebra 𝓢)) := by
  have verum : Affirms x (⟦(⊤ : F)⟧ : LindenbaumAlgebra 𝓢) := affirms_top x
  by_cases affirmed : Affirms x (⟦σ⟧ : LindenbaumAlgebra 𝓢)
  · refine NonTrivialFiber.not_factors ⟨σ, ⊤, ?_, ?_⟩
    · exact propext ⟨fun _ => verum, fun _ => affirmed⟩
    · intro same
      exact independent.1 (LindenbaumAlgebra.provable_iff_eq_top.mpr same)
  · have negated : Affirms x (⟦∼σ⟧ : LindenbaumAlgebra 𝓢) := (affirms_neg_iff 𝓢 x σ).mpr affirmed
    refine NonTrivialFiber.not_factors ⟨∼σ, ⊤, ?_, ?_⟩
    · exact propext ⟨fun _ => verum, fun _ => negated⟩
    · intro same
      exact independent.2 (LindenbaumAlgebra.provable_iff_eq_top.mpr same)

/-- Over a complete theory the Lindenbaum algebra has two values at most. -/
theorem eq_top_or_eq_bot_of_complete [Entailment.Complete 𝓢] (a : LindenbaumAlgebra 𝓢) :
    a = ⊤ ∨ a = ⊥ := by
  induction a using Quotient.ind with
  | _ φ =>
    rcases (complete_def.mp ‹Entailment.Complete 𝓢›) φ with proved | refuted
    · exact Or.inl (LindenbaumAlgebra.provable_iff_eq_top.mp proved)
    · right
      have top : (⟦φ⟧ : LindenbaumAlgebra 𝓢)ᶜ = ⊤ := by
        rw [LindenbaumAlgebra.compl_def]
        exact LindenbaumAlgebra.provable_iff_eq_top.mp refuted
      exact compl_eq_top.mp top

/-- Over a complete theory there is one completion at most. -/
theorem subsingleton_stoneSpace_of_complete [Entailment.Complete 𝓢] :
    Subsingleton (StoneSpace (LindenbaumAlgebra 𝓢)) := by
  refine ⟨fun x y => PrimeSpectrum.ext (Ideal.ext fun f => ?_)⟩
  have value : f = 1 ∨ f = 0 := by
    rcases eq_top_or_eq_bot_of_complete 𝓢 (ofBoolRing f) with top | bot
    · left
      have image := congrArg toBoolRing top
      simpa using image
    · right
      have image := congrArg toBoolRing bot
      simpa using image
  rcases value with rfl | rfl
  · constructor
    · intro hx
      exact absurd ((Ideal.eq_top_iff_one _).mpr hx) x.2.ne_top
    · intro hy
      exact absurd ((Ideal.eq_top_iff_one _).mpr hy) y.2.ne_top
  · exact ⟨fun _ => Ideal.zero_mem _, fun _ => Ideal.zero_mem _⟩

/-- **Over a complete theory every completion is isolated**: the whole space is that one
point. -/
theorem isOpen_singleton_of_complete [Entailment.Complete 𝓢]
    (x : StoneSpace (LindenbaumAlgebra 𝓢)) :
    IsOpen ({x} : Set (StoneSpace (LindenbaumAlgebra 𝓢))) := by
  have := subsingleton_stoneSpace_of_complete 𝓢
  have whole : ({x} : Set (StoneSpace (LindenbaumAlgebra 𝓢))) = Set.univ :=
    Set.eq_univ_of_forall fun y => Subsingleton.elim y x
  rw [whole]
  exact isOpen_univ

end Systems

/-! ## Arithmetic: an independent sentence -/

/-- **Two completions of a consistent `Δ₁` extension of `𝗜𝚺₁` differ on a sentence that the
theory neither proves nor refutes.** -/
theorem arithmetic_completions_disagree (T : Theory ℒₒᵣ) [𝗜𝚺₁ ⪯ T] [T.Δ₁] [Consistent T] :
    ∃ σ : Sentence ℒₒᵣ, T ⊬ σ ∧ T ⊬ ∼σ ∧
      ∃ x y : StoneSpace (LindenbaumAlgebra T),
        Affirms x (⟦σ⟧ : LindenbaumAlgebra T) ∧ Affirms y (⟦∼σ⟧ : LindenbaumAlgebra T) := by
  obtain ⟨σ, independent⟩ := incomplete_def.mp (Arithmetic.incomplete' T)
  exact ⟨σ, independent.1, independent.2, exists_disagreeing_of_independent T independent⟩

/-! ## A model is one completion -/

section Models

variable {L : Language.{u}} (T : Theory L) (M : Type v) [Nonempty M] [Structure L M]

/-- Sentences that a theory proves equivalent have the same truth value in each of its
models. -/
theorem models_iff_of_equivalent (models : M ⊧ₘ* T) {σ τ : Sentence L}
    (equivalent : T ⊢ σ ⭤ τ) : M ⊧ₘ σ ↔ M ⊧ₘ τ := by
  have holds : M ⊧ₘ (σ ⭤ τ) := models_of_provable models equivalent
  simpa using holds

/-- **The verdict of a model is a function of the class.** The truth value of a sentence in a
model of the theory depends only on the class of the sentence in the Lindenbaum algebra of the
theory: a model invents no distinction between sentences. -/
theorem model_verdict_factors_through_class (models : M ⊧ₘ* T) :
    Factors (fun σ : Sentence L => (⟦σ⟧ : LindenbaumAlgebra T))
      (fun σ : Sentence L => M ⊧ₘ σ) :=
  ⟨Quotient.lift (fun σ : Sentence L => M ⊧ₘ σ)
      (fun _ _ equivalent => propext (models_iff_of_equivalent T M models equivalent)),
    fun _ => rfl⟩

variable [L.DecidableEq]

/-- **A model is one completion.** A model of a first-order theory is a point of the space of
completions of the theory: the point affirms exactly the sentences true in the model. -/
theorem exists_completion_of_model (models : M ⊧ₘ* T) :
    ∃ x : StoneSpace (LindenbaumAlgebra T),
      ∀ σ : Sentence L, Affirms x (⟦σ⟧ : LindenbaumAlgebra T) ↔ M ⊧ₘ σ := by
  obtain ⟨verdict, factors⟩ := model_verdict_factors_through_class T M models
  have reads : ∀ σ : Sentence L, verdict ⟦σ⟧ ↔ M ⊧ₘ σ := fun σ => iff_of_eq (factors σ)
  have top : verdict ⊤ := by
    rw [LindenbaumAlgebra.top_def, reads]
    simp
  have inf : ∀ a b, verdict (a ⊓ b) ↔ verdict a ∧ verdict b := by
    intro a b
    induction a using Quotient.ind with
    | _ σ =>
      induction b using Quotient.ind with
      | _ τ =>
        rw [LindenbaumAlgebra.inf_def, reads, reads, reads]
        simp
  have compl : ∀ a, verdict aᶜ ↔ ¬ verdict a := by
    intro a
    induction a using Quotient.ind with
    | _ σ =>
      rw [LindenbaumAlgebra.compl_def, reads, reads]
      simp
  obtain ⟨x, point⟩ := exists_point_of_reading verdict top inf compl
  exact ⟨x, fun σ => (point ⟦σ⟧).trans (reads σ)⟩

/-- **One model forgets which sentences are open.** When the theory leaves some sentence open,
the class of a sentence is not a function of its truth value in a model: the model gives the
open sentence, or its negation, the truth value of a theorem. -/
theorem class_not_factors_through_model_verdict (models : M ⊧ₘ* T) {σ : Sentence L}
    (independent : Independent T σ) :
    ¬ Factors (fun τ : Sentence L => M ⊧ₘ τ)
      (fun τ : Sentence L => (⟦τ⟧ : LindenbaumAlgebra T)) := by
  obtain ⟨x, reads⟩ := exists_completion_of_model T M models
  have same : (fun τ : Sentence L => M ⊧ₘ τ) =
      fun τ : Sentence L => Affirms x (⟦τ⟧ : LindenbaumAlgebra T) :=
    funext fun τ => propext (reads τ).symm
  rw [same]
  exact class_not_factors_through_verdict T independent x

end Models

/-! ## The theory of a set model -/

section StructureTheory

variable (M : Type u) [Nonempty M] [SetStructure M]

/-- The first-order theory of a structure for the language of set theory is complete. -/
theorem structure_theory_complete : Entailment.Complete (Structure.theory ℒₛₑₜ M) := by
  refine complete_def.mpr fun σ => ?_
  by_cases holds : M ⊧ₘ σ
  · exact Or.inl (Entailment.by_axm _ (Structure.mem_theory_iff.mpr holds))
  · refine Or.inr (Entailment.by_axm _ (Structure.mem_theory_iff.mpr ?_))
    simpa using holds

/-- The first-order theory of a structure is consistent. -/
theorem structure_theory_consistent : Entailment.Consistent (Structure.theory ℒₛₑₜ M) :=
  consistent_of_satisfiable Structure.theory_satisfiable

/-- The theory of a structure has a completion. -/
theorem structureTheory_completions_nonempty :
    Nonempty (StoneSpace (LindenbaumAlgebra (Structure.theory ℒₛₑₜ M))) := by
  have := structure_theory_consistent M
  have : Nontrivial (LindenbaumAlgebra (Structure.theory ℒₛₑₜ M)) :=
    LindenbaumAlgebra.nontrivial_of_consistent
  have : Nontrivial (AsBoolRing (LindenbaumAlgebra (Structure.theory ℒₛₑₜ M))) :=
    ‹Nontrivial (LindenbaumAlgebra (Structure.theory ℒₛₑₜ M))›
  infer_instance

/-- **The theory of a set model has a strongest completion reached by one sentence**: its
completion is isolated. -/
theorem structureTheory_completion_isolated
    (x : StoneSpace (LindenbaumAlgebra (Structure.theory ℒₛₑₜ M))) :
    IsOpen ({x} : Set (StoneSpace (LindenbaumAlgebra (Structure.theory ℒₛₑₜ M)))) := by
  have := structure_theory_complete M
  exact isOpen_singleton_of_complete (Structure.theory ℒₛₑₜ M) x

end StructureTheory

/-! ## Two set models that disagree -/

/-- **Two structures that disagree on a sentence leave it open in their common theory**: the
sentences true in both neither prove nor refute it. -/
theorem common_theory_independent (M₀ : Type u) (M₁ : Type v) [Nonempty M₀] [Nonempty M₁]
    [SetStructure M₀] [SetStructure M₁] {σ : Sentence ℒₛₑₜ} (fails : ¬ M₀ ⊧ₘ σ)
    (holds : M₁ ⊧ₘ σ) :
    Independent (Structure.theory ℒₛₑₜ M₀ ∩ Structure.theory ℒₛₑₜ M₁ : Theory ℒₛₑₜ) σ := by
  have model₀ : M₀ ⊧ₘ* (Structure.theory ℒₛₑₜ M₀ ∩ Structure.theory ℒₛₑₜ M₁ : Theory ℒₛₑₜ) :=
    Structure.subset_of_models.mp Set.inter_subset_left
  have model₁ : M₁ ⊧ₘ* (Structure.theory ℒₛₑₜ M₀ ∩ Structure.theory ℒₛₑₜ M₁ : Theory ℒₛₑₜ) :=
    Structure.subset_of_models.mp Set.inter_subset_right
  refine ⟨unprovable_of_countermodel (M := M₀) fails, unprovable_of_countermodel (M := M₁) ?_⟩
  simpa using holds

/-- **The first two stages of the tower over `∅` leave the axiom of infinity open**: their
common theory neither proves nor refutes it. -/
theorem stage_theories_leave_infinity_open (h : CofinalInaccessibles.{u}) :
    Independent (Structure.theory ℒₛₑₜ (Members (stage h ∅ 0)) ∩
      Structure.theory ℒₛₑₜ (Members (stage h ∅ 1)) : Theory ℒₛₑₜ) Axiom.infinity :=
  common_theory_independent _ _ (infinity_changes h 0).1 (infinity_changes h 0).2

/-- **No later stage is elementarily equivalent to the first stage over `∅`.** Every closed set
that has the first stage as a member satisfies the axiom of infinity, which fails at the first
stage. So no later stage is an elementary extension of the first: the first stage is maximal
for elementary extension among the stages, and it is a member of the next stage. -/
theorem stage_zero_not_elementaryEquiv (h : CofinalInaccessibles.{u}) {U : ZFSet.{u}}
    (hU : Closed U) [Nonempty (Members U)] (later : stage h ∅ 0 ∈ U) :
    ¬ (Members (stage h ∅ 0) ≡ₑ[ℒₛₑₜ] Members U) := by
  intro equivalent
  have hω : ZFSet.omega ∈ U :=
    hU.subset_mem later (omega_subset_of_closed (stage_closed h ∅ 0) (empty_mem_stage h ∅ 0))
  have zfc : Members U ⊧ₘ* 𝗭𝗙𝗖 := closed_models_zfc hU hω
  have infinity : Members U ⊧ₘ Axiom.infinity :=
    (models_of_subtheory (U := 𝗭𝗙) zfc).models_set ZermeloFraenkel.axiom_of_infinity
  exact infinity_false_at_stage_zero h (equivalent.models.mpr infinity)

#print axioms affirms_compl_iff
#print axioms forall_affirms_iff
#print axioms exists_affirms_iff
#print axioms exists_point_of_reading
#print axioms forall_affirms_iff_provable
#print axioms affirms_neg_iff
#print axioms exists_disagreeing_of_independent
#print axioms class_not_factors_through_verdict
#print axioms isOpen_singleton_of_complete
#print axioms arithmetic_completions_disagree
#print axioms models_iff_of_equivalent
#print axioms model_verdict_factors_through_class
#print axioms exists_completion_of_model
#print axioms class_not_factors_through_model_verdict
#print axioms structure_theory_complete
#print axioms structure_theory_consistent
#print axioms structureTheory_completions_nonempty
#print axioms structureTheory_completion_isolated
#print axioms common_theory_independent
#print axioms stage_theories_leave_infinity_open
#print axioms stage_zero_not_elementaryEquiv

end Mettapedia.SetTheory.OpenTower.Strength.Completions
