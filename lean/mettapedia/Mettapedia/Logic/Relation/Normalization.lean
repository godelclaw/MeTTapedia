import Mathlib.Logic.Relation

/-!
# Certified normalization of an arbitrary reduction relation

A complete one-step selector computes normal forms on the accessible part of
any reduction relation. Termination is supplied separately from the selector;
confluence is needed only for uniqueness and conversion checking, not for the
normalization algorithm. No syntax, typing rules, or language encoding is fixed.

This construction abstracts the accessibility recursion originally used by the
regular two-sort dependent calculus. Relation closures and joinability are
Mathlib's `ReflTransGen`, `EqvGen`, and `Join`.
-/

namespace Mettapedia.Logic.Relation

open _root_.Relation

universe u
variable {α : Type u} {r : α → α → Prop}

/-- An element with no outgoing reduction step. -/
def IsNormal (r : α → α → Prop) (source : α) : Prop :=
  ∀ target, ¬ r source target

/-- Every reduction path from a normal element is reflexive. -/
theorem IsNormal.reflTransGen_eq {source target : α}
    (normal : IsNormal r source) (steps : ReflTransGen r source target) :
    target = source := by
  induction steps with
  | refl => rfl
  | tail _ step ih =>
      subst ih
      exact False.elim (normal _ step)

/-- Confluence joins any two finite reductions from the same source. -/
def Confluent (r : α → α → Prop) : Prop :=
  ∀ source left right, ReflTransGen r source left →
    ReflTransGen r source right → Join (ReflTransGen r) left right

/-- Newman's lemma: terminating local forks give confluence of finite paths. -/
theorem confluent_of_accessible_forks
    (accessible : ∀ source, Acc (fun target source => r source target) source)
    (forks : ∀ source left right, r source left → r source right →
      Join (ReflTransGen r) left right) : Confluent r := by
  intro source
  induction accessible source with
  | intro source _ ih =>
      intro left right leftSteps rightSteps
      rcases leftSteps.cases_head with same | ⟨first, firstStep, leftRest⟩
      · subst left
        exact ⟨right, rightSteps, .refl⟩
      · rcases rightSteps.cases_head with same | ⟨second, secondStep, rightRest⟩
        · subst right
          exact ⟨left, .refl, leftSteps⟩
        · obtain ⟨middle, firstJoin, secondJoin⟩ := forks source first second firstStep secondStep
          obtain ⟨next, leftJoin, middleJoin⟩ := ih first firstStep left middle leftRest firstJoin
          obtain ⟨final, rightJoin, nextJoin⟩ :=
            ih second secondStep right next rightRest (secondJoin.trans middleJoin)
          exact ⟨final, leftJoin.trans nextJoin, rightJoin⟩

/-- Under confluence, the equivalence closure is exactly joinability. -/
theorem Confluent.eqvGen_iff_join (confluent : Confluent r) {left right : α} :
    EqvGen r left right ↔ Join (ReflTransGen r) left right := by
  constructor
  · intro conversion
    exact (equivalence_join confluent).eqvGen_iff.mp
      (EqvGen.mono (fun _ target step =>
        ⟨target, ReflTransGen.single step, ReflTransGen.refl⟩) _ _ conversion)
  · rintro ⟨common, leftSteps, rightSteps⟩
    exact EqvGen.trans _ _ _ (EqvGen.reflTransGen_le_eqvGen r _ _ leftSteps)
      (EqvGen.symm _ _ (EqvGen.reflTransGen_le_eqvGen r _ _ rightSteps))

/-- A normal form together with the actual reduction and irreducibility proofs. -/
structure NormalizationResult (r : α → α → Prop) (source : α) where
  normalForm : α
  reduces : ReflTransGen r source normalForm
  irreducible : IsNormal r normalForm

/-- Accessibility implies existence of a reachable normal element. This
classical existence theorem is separate from the executable selector below. -/
theorem exists_normalForm_of_acc {source : α}
    (accessible : Acc (fun target source => r source target) source) :
    ∃ target, ReflTransGen r source target ∧ IsNormal r target := by
  classical
  induction accessible with
  | intro source _ ih =>
      by_cases normal : IsNormal r source
      · exact ⟨source, ReflTransGen.refl, normal⟩
      · have nextExists : ∃ next, r source next :=
          Classical.byContradiction (fun denied => normal (fun next step => denied ⟨next, step⟩))
        obtain ⟨next, step⟩ := nextExists
        obtain ⟨target, steps, finished⟩ := ih next step
        exact ⟨target, ReflTransGen.head step steps, finished⟩

/-- Accessibility is retained when a recursive call follows a nonempty path. -/
theorem accessible_transitiveClosure {source : α} (accessible : Acc r source) :
    Acc (TransGen r) source := by
  induction accessible with
  | intro source _ ih =>
      refine Acc.intro source ?_
      intro target steps
      cases steps with
      | single step => exact ih target step
      | tail before last => exact (ih _ last).inv before

/-- Strong postponement preserves termination when two terminating relations
are interleaved. The first relation retains a nonempty path when moved before
one step of the second relation. -/
theorem stronglyNormalizing_union_of_postponement {s : α → α → Prop}
    (left : ∀ source, Acc (fun target source => r source target) source)
    (right : ∀ source, Acc (fun target source => s source target) source)
    (postpones : ∀ {source middle target}, s source middle → TransGen r middle target →
      ∃ next, TransGen r source next ∧ ReflTransGen s next target) :
    ∀ source, Acc (fun target source => r source target ∨ s source target) source := by
  have carry {source target : α}
      (accessible : Acc (fun target source => r source target ∨ s source target) source)
      (steps : ReflTransGen s source target) :
      Acc (fun target source => r source target ∨ s source target) target := by
    induction steps with
    | refl => exact accessible
    | tail _ step ih => exact ih.inv (Or.inr step)
  have alongRight (source : α) (accessible : Acc (fun target source => s source target) source) :
      (∀ target, TransGen r source target →
        Acc (fun target source => r source target ∨ s source target) target) →
      Acc (fun target source => r source target ∨ s source target) source := by
    induction accessible with
    | intro source _ ih =>
        intro descendants
        refine Acc.intro source ?_
        intro target step
        rcases step with first | second
        · exact descendants target (.single first)
        · apply ih target second
          intro next after
          obtain ⟨middle, moved, last⟩ := postpones second after
          exact carry (descendants middle moved) last
  intro source
  induction left source with
  | intro source _ ih =>
      apply alongRight source (right source)
      intro target steps
      induction steps with
      | single step => exact ih _ step
      | tail _ step ready => exact ready.inv (Or.inl step)

/-- Convertible sources have equal normal forms in a confluent relation.
The normal forms can come from different algorithms. -/
theorem NormalizationResult.eq_of_eqvGen (confluent : Confluent r)
    {left right : α} (leftResult : NormalizationResult r left)
    (rightResult : NormalizationResult r right) (conversion : EqvGen r left right) :
    leftResult.normalForm = rightResult.normalForm := by
  have normalConversion := EqvGen.trans _ _ _
    (EqvGen.symm _ _ (EqvGen.reflTransGen_le_eqvGen r _ _ leftResult.reduces))
    (EqvGen.trans _ _ _ conversion
      (EqvGen.reflTransGen_le_eqvGen r _ _ rightResult.reduces))
  obtain ⟨common, leftSteps, rightSteps⟩ := confluent.eqvGen_iff_join.mp normalConversion
  exact (leftResult.irreducible.reflTransGen_eq leftSteps).symm.trans
    (rightResult.irreducible.reflTransGen_eq rightSteps)

/-- Comparing certified normal forms decides conversion wherever both results
are available; global termination is not required. -/
theorem NormalizationResult.eq_iff_eqvGen (confluent : Confluent r)
    {left right : α} (leftResult : NormalizationResult r left)
    (rightResult : NormalizationResult r right) :
    leftResult.normalForm = rightResult.normalForm ↔ EqvGen r left right := by
  constructor
  · intro same
    apply confluent.eqvGen_iff_join.mpr
    exact ⟨leftResult.normalForm, leftResult.reduces, same ▸ rightResult.reduces⟩
  · exact leftResult.eq_of_eqvGen confluent rightResult

/-- An executable selector that fails exactly at normal elements. The returned
subtype certifies soundness; completeness does not require selecting every step. -/
structure CompleteStepSelector (r : α → α → Prop) where
  step : (source : α) → Option {target // r source target}
  none_iff_normal : ∀ source, step source = none ↔ IsNormal r source

/-- Iterate a complete selector using strong normalization at the source.
The accessibility relation reverses the reduction arguments so that recursive
calls follow outgoing steps. The accessibility proof is erased at execution. -/
def CompleteStepSelector.normalize (selector : CompleteStepSelector r) (source : α)
    (accessible : Acc (fun target source => r source target) source) :
    NormalizationResult r source := by
  induction accessible with
  | intro term _ ih =>
      cases selected : selector.step term with
      | none =>
          exact ⟨term, ReflTransGen.refl, (selector.none_iff_normal term).mp selected⟩
      | some next =>
          let result := ih next.1 next.2
          exact ⟨result.normalForm, ReflTransGen.head next.2 result.reduces,
            result.irreducible⟩

/-- All complete selectors compute the same normal form on a confluent,
accessible source. This asserts equality of results, not of execution routes. -/
theorem CompleteStepSelector.normalize_strategy_independent
    (confluent : Confluent r) (first second : CompleteStepSelector r) (source : α)
    (accessible : Acc (fun target source => r source target) source) :
    (first.normalize source accessible).normalForm =
      (second.normalize source accessible).normalForm :=
  (first.normalize source accessible).eq_of_eqvGen confluent
    (second.normalize source accessible) (EqvGen.refl source)

end Mettapedia.Logic.Relation
