import Mettapedia.GSLT.Logic.InterfaceObservationKitEmbedding

/-!
# Monotonic admission of actual observation contexts

Restricting a kit by an independently supplied predicate retains the complete
selected labels and their arrows. Every restricted formula embeds into the
original grammar with the same depth and satisfaction. Agreement for the
original kit therefore implies agreement for the restricted one.

The result changes observer admission. It does not restrict reaction rules,
change their firing semantics or infer an executor for arbitrary predicates.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.InterfaceObservationKit

open _root_.CategoryTheory RedexRelativeCongruence

universe u v uIndex uLabel

variable {C : Type u} [Category.{v} C] {Index : Type uIndex}
  (K : Kit.{u, v, uIndex, uLabel} C Index)
  (admitted : ∀ {first last : Index}, K.Label first last → Prop)

def restrict : Kit.{u, v, uIndex, uLabel} C Index where
  object := K.object
  Label first last := {label : K.Label first last // admitted label}
  context label := K.context label.val

instance restricted_labels_finite [∀ first last, Finite (K.Label first last)] (first last : Index) :
    Finite ((restrict K admitted).Label first last) := by
  change Finite {label : K.Label first last // admitted label}
  infer_instance

def Formula.expand : {interface : Index} → Formula (restrict K admitted) interface → Formula K interface
  | _, .top => .top
  | _, .conj first second => .conj first.expand second.expand
  | _, .neg inner => .neg inner.expand
  | _, .diamond label inner => .diamond label.val inner.expand

theorem expand_depth {interface : Index} (formula : Formula (restrict K admitted) interface) :
    formula.expand.depth = formula.depth := by
  induction formula with
  | top => rfl
  | conj first second firstRead secondRead =>
      change max first.expand.depth second.expand.depth = max first.depth second.depth
      rw [firstRead, secondRead]
  | neg inner inductionHypothesis => exact inductionHypothesis
  | diamond label inner inductionHypothesis => exact congrArg (· + 1) inductionHypothesis

variable (origin : C) (rules : ReactionRule origin → Prop)

theorem restricted_satisfaction {interface : Index} (formula : Formula (restrict K admitted) interface) :
    ∀ agent : origin ⟶ K.object interface,
      Holds K origin rules formula.expand agent ↔ Holds (restrict K admitted) origin rules formula agent := by
  induction formula with
  | top => intro agent; exact Iff.rfl
  | conj first second firstRead secondRead =>
      intro agent
      exact and_congr (firstRead agent) (secondRead agent)
  | neg inner inductionHypothesis => intro agent; exact not_congr (inductionHypothesis agent)
  | diamond label inner inductionHypothesis =>
      intro agent
      exact exists_congr fun target => and_congr Iff.rfl (inductionHypothesis target)

theorem observation_agreement_restricts (depth : Nat) {interface : Index}
    {first second : origin ⟶ K.object interface}
    (related : LogicallyEquivalent K origin rules depth first second) :
    LogicallyEquivalent (restrict K admitted) origin rules depth first second := by
  intro formula bounded
  exact (restricted_satisfaction K admitted origin rules formula first).symm.trans
    ((related formula.expand (le_of_eq_of_le (expand_depth K admitted formula) bounded)).trans
      (restricted_satisfaction K admitted origin rules formula second))

theorem actual_round_agreement_restricts (depth : Nat) {interface : Index}
    {first second : origin ⟶ K.object interface}
    (related : Rounds K origin rules depth first second) :
    Rounds (restrict K admitted) origin rules depth first second := by
  induction depth generalizing interface first second with
  | zero => exact True.intro
  | succ depth inductionHypothesis =>
      constructor
      · intro last label target actual
        obtain ⟨matched, firing, compared⟩ := related.1 last label.val target actual
        exact ⟨matched, firing, inductionHypothesis compared⟩
      · intro last label target actual
        obtain ⟨matched, firing, compared⟩ := related.2 last label.val target actual
        exact ⟨matched, firing, inductionHypothesis compared⟩

end Mettapedia.GSLT.InterfaceObservationKit
