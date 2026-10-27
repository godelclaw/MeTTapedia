import Mettapedia.Logic.Relation.NormalFormDecision

/-!
# The admission criterion for promoted rules, for any reduction relation

A bubble decides its conversion by reducing both sides to normal form and comparing them. A
justified equation added to the bubble's steps keeps every conversion sound, but it can break
the decision: the reduction may stop being confluent, or stop terminating. This module states
what a promotion must carry so that the decision survives, for an arbitrary relation.

* **The criterion** (`Convergent`): the steps after promotion (`promoted base delta`) are
  locally confluent (every one-step fork joins) and terminating (every reduction is finite).
* **What it buys** (`Convergent.confluent`, `Convergent.normalForm_exists`,
  `Convergent.normalForm_unique`, `Convergent.decidedOn`): by Newman's lemma the steps are
  confluent; every element has exactly one normal form; and conversion is decided by normal
  forms on every set, which places the promoted bubble in the normal-form fiber
  (`Logic.Relation.DecidedOn`) everywhere. Any complete step selector computes the normal form
  (`Convergent.normalize_decides`).
* **Justification is separate** (`conv_sound_of_justified`): if every step is justified by an
  equivalence (equality in a model), so is every conversion. A justification gives soundness,
  never the decision.
* **The criterion is exactly convergence** (`convergent_iff`): it holds exactly when the steps
  are confluent and terminating. Termination cannot be weakened to weak normalization: the
  control `Controls.Kleene` (Kleene's example, as in Huet 1980) is locally confluent, every
  element has a normal form, and conversion is not decided by normal forms. Local confluence
  cannot be dropped either: a terminating fork to two normal forms (`Controls.fork`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.PromotionAdmission

universe u

open Relation
open Mettapedia.Logic.Relation (Confluent IsNormal IsNormalFormOf DecidedOn WeaklyNormalizingOn
  NormalizationResult CompleteStepSelector confluent_of_accessible_forks exists_normalForm_of_acc
  decidedOn_of_confluent)

variable {α : Type u}

/-- Every one-step fork joins. -/
def LocallyConfluent (r : α → α → Prop) : Prop :=
  ∀ a b c, r a b → r a c → Join (ReflTransGen r) b c

/-- Every reduction is finite. -/
def Terminating (r : α → α → Prop) : Prop :=
  ∀ a, Acc (fun target source => r source target) a

/-- The steps of a bubble after promoting the steps `delta` into its steps `base`. -/
def promoted (base delta : α → α → Prop) : α → α → Prop :=
  fun a b => base a b ∨ delta a b

/-- **The admission criterion**: locally confluent and terminating. -/
structure Convergent (r : α → α → Prop) : Prop where
  locallyConfluent : LocallyConfluent r
  terminating : Terminating r

namespace Convergent

variable {r : α → α → Prop} (h : Convergent r)
include h

/-- **Newman's lemma.** -/
theorem confluent : Confluent r :=
  confluent_of_accessible_forks h.terminating fun a b c first second =>
    h.locallyConfluent a b c first second

/-- Every element has a normal form. -/
theorem normalForm_exists (a : α) : ∃ n, IsNormalFormOf r a n :=
  exists_normalForm_of_acc (h.terminating a)

/-- The normal form is unique. -/
theorem normalForm_unique {a n m : α} (first : IsNormalFormOf r a n)
    (second : IsNormalFormOf r a m) : n = m := by
  obtain ⟨common, fromN, fromM⟩ := h.confluent a n m first.1 second.1
  exact (first.2.reflTransGen_eq fromN).symm.trans (second.2.reflTransGen_eq fromM)

/-- **Conversion is decided by normal forms on every set**: the promoted bubble is in the
normal-form fiber everywhere. -/
theorem decidedOn (S : Set α) : DecidedOn r S :=
  decidedOn_of_confluent h.confluent fun a _ => h.normalForm_exists a

/-- Conversion is joinability. -/
theorem conv_iff_join {a b : α} : EqvGen r a b ↔ Join (ReflTransGen r) a b :=
  h.confluent.eqvGen_iff_join

/-- **Normal forms computed by any complete step selector decide conversion.** -/
theorem normalize_decides (selector : CompleteStepSelector r) (a b : α) :
    (selector.normalize a (h.terminating a)).normalForm =
        (selector.normalize b (h.terminating b)).normalForm ↔ EqvGen r a b :=
  NormalizationResult.eq_iff_eqvGen h.confluent _ _

end Convergent

/-- **The criterion is exactly convergence.** -/
theorem convergent_iff {r : α → α → Prop} : Convergent r ↔ Confluent r ∧ Terminating r := by
  constructor
  · intro h; exact ⟨h.confluent, h.terminating⟩
  · rintro ⟨confluent, terminating⟩
    exact ⟨fun a b c first second =>
      confluent a b c (ReflTransGen.single first) (ReflTransGen.single second), terminating⟩

/-- **Justified steps give sound conversions**: an equivalence that contains every step
contains every conversion. -/
theorem conv_sound_of_justified {r valid : α → α → Prop} (equivalence : Equivalence valid)
    (justify : ∀ a b, r a b → valid a b) {a b : α} (converted : EqvGen r a b) : valid a b := by
  induction converted with
  | rel _ _ step => exact justify _ _ step
  | refl => exact equivalence.refl _
  | symm _ _ _ ih => exact equivalence.symm ih
  | trans _ _ _ _ _ first second => exact equivalence.trans first second

/-- **Promotion, admitted**: justified steps on both sides and a convergent promotion keep
every conversion sound and decide conversion by normal forms on every set. -/
theorem promoted_admitted {base delta valid : α → α → Prop} (equivalence : Equivalence valid)
    (justifiedBase : ∀ a b, base a b → valid a b) (justifiedDelta : ∀ a b, delta a b → valid a b)
    (convergent : Convergent (promoted base delta)) :
    (∀ {a b}, EqvGen (promoted base delta) a b → valid a b) ∧ Confluent (promoted base delta) ∧
      ∀ S, DecidedOn (promoted base delta) S :=
  ⟨conv_sound_of_justified equivalence fun a b step => step.elim (justifiedBase a b)
      (justifiedDelta a b), convergent.confluent, convergent.decidedOn⟩

/-- A step of the base is a step after promotion. -/
theorem promoted_base {base delta : α → α → Prop} {a b : α} (step : base a b) :
    promoted base delta a b := Or.inl step

/-- A promoted step is a step after promotion. -/
theorem promoted_delta {base delta : α → α → Prop} {a b : α} (step : delta a b) :
    promoted base delta a b := Or.inr step

/-! ## Controls -/

namespace Controls

/-- Four states for Kleene's example. -/
inductive KleeneState where
  | a | b | c | d
  deriving DecidableEq

open KleeneState

/-- `b ↦ a`, `b ↦ c`, `c ↦ b`, `c ↦ d`. -/
inductive Kleene : KleeneState → KleeneState → Prop where
  | ba : Kleene b a
  | bc : Kleene b c
  | cb : Kleene c b
  | cd : Kleene c d

theorem a_normal : IsNormal Kleene a := by intro t step; cases step

theorem d_normal : IsNormal Kleene d := by intro t step; cases step

theorem c_to_a : ReflTransGen Kleene c a := ReflTransGen.head .cb (ReflTransGen.single .ba)

theorem b_to_d : ReflTransGen Kleene b d := ReflTransGen.head .bc (ReflTransGen.single .cd)

/-- **Kleene's example is locally confluent.** -/
theorem kleene_locallyConfluent : LocallyConfluent Kleene := by
  intro x y z first second
  cases first <;> cases second
  all_goals first
    | exact ⟨_, .refl, .refl⟩
    | exact ⟨a, .refl, c_to_a⟩
    | exact ⟨a, c_to_a, .refl⟩
    | exact ⟨d, b_to_d, .refl⟩
    | exact ⟨d, .refl, b_to_d⟩

/-- **Every element has a normal form.** -/
theorem kleene_weaklyNormalizing : WeaklyNormalizingOn Kleene Set.univ := by
  intro x _
  cases x with
  | a => exact ⟨a, .refl, a_normal⟩
  | b => exact ⟨a, ReflTransGen.single .ba, a_normal⟩
  | c => exact ⟨d, ReflTransGen.single .cd, d_normal⟩
  | d => exact ⟨d, .refl, d_normal⟩

/-- **And it is not confluent**: `b` reaches the two normal forms `a` and `d`. -/
theorem kleene_not_confluent : ¬ Confluent Kleene := by
  intro confluent
  obtain ⟨w, fromA, fromD⟩ := confluent b a d (ReflTransGen.single .ba) b_to_d
  have := (a_normal.reflTransGen_eq fromA).symm.trans (d_normal.reflTransGen_eq fromD)
  cases this

/-- **So it is not convergent**: termination fails (`b ↦ c ↦ b`). -/
theorem kleene_not_terminating : ¬ Terminating Kleene := by
  intro terminating
  have claim : ∀ x, Acc (fun target source => Kleene source target) x → x ≠ b ∧ x ≠ c := by
    intro x accessible
    induction accessible with
    | intro x _ ih =>
        refine ⟨fun same => ?_, fun same => ?_⟩
        · subst same; exact (ih c .bc).2 rfl
        · subst same; exact (ih b .cb).1 rfl
  exact (claim b (terminating b)).1 rfl

/-- **Conversion is not decided by normal forms**: weak normalization with local confluence
is not enough; termination is the hypothesis Newman's lemma needs. -/
theorem kleene_not_decided : ¬ DecidedOn Kleene Set.univ := by
  intro decided
  have := (decided.2 a trivial d trivial a d ⟨.refl, a_normal⟩ ⟨.refl, d_normal⟩).mp
    (EqvGen.trans _ _ _ (EqvGen.symm _ _ (EqvGen.rel _ _ .ba))
      (EqvGen.trans _ _ _ (EqvGen.rel _ _ .bc) (EqvGen.rel _ _ .cd)))
  cases this

/-- A terminating fork to two normal forms. -/
inductive Fork : KleeneState → KleeneState → Prop where
  | left : Fork b a
  | right : Fork b d

theorem fork_terminating : Terminating Fork := by
  have normalA : ∀ t, ¬ Fork a t := by intro t step; cases step
  have normalD : ∀ t, ¬ Fork d t := by intro t step; cases step
  intro x
  cases x with
  | a => exact Acc.intro _ fun t step => absurd step (normalA t)
  | b =>
      refine Acc.intro _ fun t step => ?_
      cases step
      · exact Acc.intro _ fun t step => absurd step (normalA t)
      · exact Acc.intro _ fun t step => absurd step (normalD t)
  | c => exact Acc.intro _ fun t step => by cases step
  | d => exact Acc.intro _ fun t step => absurd step (normalD t)

/-- **Terminating is not enough**: the fork is not locally confluent. -/
theorem fork_not_locallyConfluent : ¬ LocallyConfluent Fork := by
  intro lc
  obtain ⟨w, fromA, fromD⟩ := lc b a d .left .right
  have normalA : IsNormal Fork a := by intro t step; cases step
  have normalD : IsNormal Fork d := by intro t step; cases step
  have := (normalA.reflTransGen_eq fromA).symm.trans (normalD.reflTransGen_eq fromD)
  cases this

end Controls

/-! ## Axiom audit -/

#print axioms Convergent.confluent
#print axioms Convergent.decidedOn
#print axioms Convergent.normalize_decides
#print axioms convergent_iff
#print axioms promoted_admitted
#print axioms Controls.kleene_locallyConfluent
#print axioms Controls.kleene_not_decided
#print axioms Controls.fork_not_locallyConfluent

end Mettapedia.TypeTheory.PromotionAdmission
