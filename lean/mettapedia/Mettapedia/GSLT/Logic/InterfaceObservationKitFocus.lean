import Mettapedia.GSLT.Logic.InterfaceObservationKit

/-!
# Typed reading of the complete admitted modal grammar

Every total-system formula has an independent reading at each interface.
An interface atom becomes truth or falsity there. A context with a different
source cannot fire and likewise reads as falsity. Matching contexts retain
the original arrow and recurse at their actual result interface.

This earns both satisfaction and depth comparisons; it does not identify a
selected kit with the unrestricted context language.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.InterfaceObservationKit

open _root_.CategoryTheory RedexRelativeCongruence

universe u v uIndex uLabel

variable {C : Type u} [Category.{v} C] {Index : Type uIndex}
  (K : Kit.{u, v, uIndex, uLabel} C Index) (origin : C)
  (rules : ReactionRule origin → Prop)

theorem step_source_interface {label : TotalLabel K} {source target : State K origin}
    (firing : Step K origin rules label source target) : source.1 = label.1 := by
  cases firing
  rfl

noncomputable def focus : HennessyMilner.Formula Index (TotalLabel K) →
    (interface : Index) → Formula K interface := by
  classical
  exact fun formula => match formula with
    | .top => fun _ => .top
    | .atom atom => fun interface => if atom = interface then .top else .neg .top
    | .conj first second => fun interface => .conj (focus first interface) (focus second interface)
    | .neg inner => fun interface => .neg (focus inner interface)
    | .dia label inner => fun interface =>
        if same : label.1 = interface then
          same ▸ Formula.diamond label.2.2 (focus inner label.2.1)
        else .neg .top

theorem focus_depth (formula : HennessyMilner.Formula Index (TotalLabel K)) :
    ∀ interface : Index, (focus K formula interface).depth ≤ formula.depth := by
  classical
  induction formula with
  | top => intro interface; exact Nat.le_refl 0
  | atom atom =>
      intro interface
      by_cases same : atom = interface <;> simp [focus, same, Formula.depth, HennessyMilner.Formula.depth]
  | conj first second firstRead secondRead =>
      intro interface
      exact max_le_max (firstRead interface) (secondRead interface)
  | neg inner inductionHypothesis => intro interface; exact inductionHypothesis interface
  | dia label inner inductionHypothesis =>
      intro interface
      rcases label with ⟨first, last, label⟩
      by_cases same : first = interface
      · subst interface
        simp only [focus]
        exact Nat.add_le_add_right (inductionHypothesis last) 1
      · simp [focus, same, Formula.depth, HennessyMilner.Formula.depth]

theorem focus_satisfaction (formula : HennessyMilner.Formula Index (TotalLabel K)) :
    ∀ (interface : Index) (agent : origin ⟶ K.object interface),
      Holds K origin rules (focus K formula interface) agent ↔
        (system K origin rules).sat formula ⟨interface, agent⟩ := by
  classical
  induction formula with
  | top => intro interface agent; exact Iff.rfl
  | atom atom =>
      intro interface agent
      by_cases same : atom = interface
      · subst atom
        change Holds K origin rules (if interface = interface then .top else .neg .top) agent ↔
          interface = interface
        simp [Holds]
      · change Holds K origin rules (if atom = interface then .top else .neg .top) agent ↔
          interface = atom
        simp [same, Ne.symm same, Holds]
  | conj first second firstRead secondRead =>
      intro interface agent
      exact and_congr (firstRead interface agent) (secondRead interface agent)
  | neg inner inductionHypothesis =>
      intro interface agent
      exact not_congr (inductionHypothesis interface agent)
  | dia label inner inductionHypothesis =>
      intro interface agent
      rcases label with ⟨first, last, label⟩
      by_cases same : first = interface
      · subst interface
        simp only [focus]
        constructor
        · rintro ⟨target, actual, held⟩
          exact ⟨⟨last, target⟩, Step.actual label agent target actual,
            (inductionHypothesis last target).mp held⟩
        · rintro ⟨target, actual, held⟩
          cases actual with
          | actual _ _ target firing =>
              exact ⟨target, firing, (inductionHypothesis last target).mpr held⟩
      · simp only [focus, dif_neg same]
        constructor
        · intro impossible
          exact (impossible True.intro).elim
        · rintro ⟨target, actual, _held⟩
          have source := step_source_interface K origin rules actual
          exact (same source.symm).elim

def LogicallyEquivalent (depth : Nat) {interface : Index}
    (first second : origin ⟶ K.object interface) : Prop :=
  ∀ formula : Formula K interface, formula.depth ≤ depth →
    (Holds K origin rules formula first ↔ Holds K origin rules formula second)

theorem logical_comparison (depth : Nat) {interface : Index}
    (first second : origin ⟶ K.object interface) :
    LogicallyEquivalent K origin rules depth first second ↔
      HennessyMilner.FiniteDepth.LogicallyEquivalent (system K origin rules) depth
        ⟨interface, first⟩ ⟨interface, second⟩ := by
  constructor
  · intro related formula bounded
    exact (focus_satisfaction K origin rules formula interface first).symm.trans
      ((related (focus K formula interface) (le_trans (focus_depth K formula interface) bounded)).trans
        (focus_satisfaction K origin rules formula interface second))
  · intro related formula bounded
    exact (erase_satisfaction K origin rules formula first).symm.trans
      ((related formula.erase (le_of_eq_of_le (erase_depth K formula) bounded)).trans
        (erase_satisfaction K origin rules formula second))

end Mettapedia.GSLT.InterfaceObservationKit
