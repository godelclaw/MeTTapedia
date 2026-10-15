import Mettapedia.GSLT.Logic.InterfaceObservationKitFocus

/-!
# Complete bounded observations of admitted context interactions

Round agreement is independently defined using actual context-labelled
firings at each interface. The typed modal grammar characterizes those
rounds for finite actual interface and label carriers. No branching bound
is required. Characteristic tests are constructed at the proper interface.

The conclusion concerns admitted contexts; neither unrestricted interaction
nor test execution cost is inferred from this observation depth.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.InterfaceObservationKit

open _root_.CategoryTheory RedexRelativeCongruence

universe u v uIndex uLabel

variable {C : Type u} [Category.{v} C] {Index : Type uIndex}
  (K : Kit.{u, v, uIndex, uLabel} C Index) (origin : C)
  (rules : ReactionRule origin → Prop)

def Rounds : Nat → {interface : Index} →
    (origin ⟶ K.object interface) → (origin ⟶ K.object interface) → Prop
  | 0, _, _, _ => True
  | depth + 1, _, first, second =>
      (∀ (last : Index) (label : K.Label _ last) (target : origin ⟶ K.object last),
        ActIPO rules (K.context label) first target →
          ∃ matched, ActIPO rules (K.context label) second matched ∧ Rounds depth target matched) ∧
      (∀ (last : Index) (label : K.Label _ last) (target : origin ⟶ K.object last),
        ActIPO rules (K.context label) second target →
          ∃ matched, ActIPO rules (K.context label) first matched ∧ Rounds depth matched target)

theorem round_comparison (depth : Nat) :
    ∀ {interface : Index} (first second : origin ⟶ K.object interface),
      Rounds K origin rules depth first second ↔
        HennessyMilner.FiniteDepth.Rounds (system K origin rules) depth
          ⟨interface, first⟩ ⟨interface, second⟩ := by
  induction depth with
  | zero =>
      intro interface first second
      constructor
      · intro _ atom
        exact Iff.rfl
      · intro _
        exact True.intro
  | succ depth inductionHypothesis =>
      intro interface first second
      constructor
      · intro related
        refine ⟨fun _ => Iff.rfl, ?_, ?_⟩
        · intro label target actual
          cases actual with
          | actual label first target firing =>
              obtain ⟨matched, actual, compared⟩ := related.1 _ label target firing
              exact ⟨⟨_, matched⟩, Step.actual label second matched actual,
                (inductionHypothesis target matched).mp compared⟩
        · intro label target actual
          cases actual with
          | actual label second target firing =>
              obtain ⟨matched, actual, compared⟩ := related.2 _ label target firing
              exact ⟨⟨_, matched⟩, Step.actual label first matched actual,
                (inductionHypothesis matched target).mp compared⟩
      · intro related
        constructor
        · intro last label target firing
          obtain ⟨matched, actual, compared⟩ :=
            related.2.1 ⟨interface, last, label⟩ ⟨last, target⟩
              (Step.actual label first target firing)
          cases actual with
          | actual _ _ matched firing =>
              exact ⟨matched, firing, (inductionHypothesis target matched).mpr compared⟩
        · intro last label target firing
          obtain ⟨matched, actual, compared⟩ :=
            related.2.2 ⟨interface, last, label⟩ ⟨last, target⟩
              (Step.actual label second target firing)
          cases actual with
          | actual _ _ matched firing =>
              exact ⟨matched, firing, (inductionHypothesis matched target).mpr compared⟩

variable [Finite Index] [∀ first last, Finite (K.Label first last)]

instance system_atoms_finite : Finite (system K origin rules).Atom := by
  change Finite Index
  infer_instance

instance system_labels_finite : Finite (system K origin rules).Label := by
  change Finite (TotalLabel K)
  infer_instance

theorem bounded_adequacy (depth : Nat) {interface : Index}
    (first second : origin ⟶ K.object interface) :
    LogicallyEquivalent K origin rules depth first second ↔ Rounds K origin rules depth first second :=
  (logical_comparison K origin rules depth first second).trans
    ((HennessyMilner.FiniteDepth.logicallyEquivalent_iff_rounds
      (system K origin rules) depth ⟨interface, first⟩ ⟨interface, second⟩).trans
        (round_comparison K origin rules depth first second).symm)

noncomputable def characteristic (depth : Nat) {interface : Index}
    (agent : origin ⟶ K.object interface) : Formula K interface :=
  focus K
    (HennessyMilner.FiniteDepth.characteristic depth
      (HennessyMilner.FiniteDepth.reading (system K origin rules) depth ⟨interface, agent⟩)) interface

theorem characteristic_depth (depth : Nat) {interface : Index}
    (agent : origin ⟶ K.object interface) :
    (characteristic K origin rules depth agent).depth ≤ depth :=
  le_trans (focus_depth K _ interface)
    (HennessyMilner.FiniteDepth.characteristic_depth depth _)

theorem characteristic_readout (depth : Nat) {interface : Index}
    (agent target : origin ⟶ K.object interface) :
    Holds K origin rules (characteristic K origin rules depth agent) target ↔
      Rounds K origin rules depth agent target := by
  have tests := HennessyMilner.FiniteDepth.characteristic_satisfaction
    (system K origin rules) depth
      (HennessyMilner.FiniteDepth.reading (system K origin rules) depth ⟨interface, agent⟩)
      ⟨interface, target⟩
  constructor
  · intro held
    have same := tests.mp ((focus_satisfaction K origin rules _ interface target).mp held)
    exact (round_comparison K origin rules depth agent target).mpr
      ((HennessyMilner.FiniteDepth.rounds_iff_reading_eq
        (system K origin rules) depth ⟨interface, agent⟩ ⟨interface, target⟩).mpr same.symm)
  · intro related
    have same := (HennessyMilner.FiniteDepth.rounds_iff_reading_eq
      (system K origin rules) depth ⟨interface, agent⟩ ⟨interface, target⟩).mp
        ((round_comparison K origin rules depth agent target).mp related)
    exact (focus_satisfaction K origin rules _ interface target).mpr (tests.mpr same.symm)

end Mettapedia.GSLT.InterfaceObservationKit
