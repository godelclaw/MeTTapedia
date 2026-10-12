import Mettapedia.GSLT.Logic.InterfaceModalLogic
import Mettapedia.GSLT.Logic.FiniteDepthHennessyMilnerCharacteristic
import Mathlib.Data.Finite.Sigma

/-!
# Admitted observations at actual reaction interfaces

A kit selects interfaces and complete context arrows between them. Its
independent typed formula grammar observes the existing idem-pushout firing
relation. The total labelled system retains both ends of every context and
the actual target agent. Its atomic readings record only the interface.

Finiteness, when supplied, concerns the actual index and label carriers. A
finite presentation of instruments does not supply those hypotheses.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.InterfaceObservationKit

open _root_.CategoryTheory RedexRelativeCongruence

universe u v uIndex uLabel

structure Kit (C : Type u) [Category.{v} C] (Index : Type uIndex) where
  object : Index → C
  Label : Index → Index → Type uLabel
  context : ∀ {first last}, Label first last → (object first ⟶ object last)

variable {C : Type u} [Category.{v} C] {Index : Type uIndex}
  (K : Kit.{u, v, uIndex, uLabel} C Index) (origin : C)

abbrev State := (interface : Index) × (origin ⟶ K.object interface)

abbrev TotalLabel := (first : Index) × (last : Index) × K.Label first last

instance totalLabel_finite [Finite Index] [∀ first last, Finite (K.Label first last)] :
    Finite (TotalLabel K) := by
  infer_instance

variable (rules : ReactionRule origin → Prop)

inductive Step : (TotalLabel K) → (State K origin) → (State K origin) → Prop
  | actual {first last : Index} (label : K.Label first last)
      (agent : origin ⟶ K.object first) (target : origin ⟶ K.object last)
      (firing : ActIPO rules (K.context label) agent target) :
      Step ⟨first, last, label⟩ ⟨first, agent⟩ ⟨last, target⟩

def theory : GSLT where
  Term := (State K origin)
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites first second := ∃ label, Step K origin rules label first second
  rewrites_resp_left := by
    rintro first _ second rfl firing
    exact ⟨second, firing, rfl⟩
  rewrites_resp_right := by
    rintro first second _ firing rfl
    exact firing

def system : HennessyMilner.System (theory K origin rules) where
  Atom := Index
  observes interface state := state.1 = interface
  observes_resp := by
    rintro interface first _ rfl
    exact Iff.rfl
  Label := (TotalLabel K)
  act := Step K origin rules
  act_resp_left := by
    rintro label first _ second rfl firing
    exact ⟨second, firing, rfl⟩
  act_resp_right := by
    rintro label first second _ firing rfl
    exact firing

theorem step_at_interfaces_iff {first last : Index} (label : K.Label first last)
    (agent : origin ⟶ K.object first) (target : origin ⟶ K.object last) :
    Step K origin rules ⟨first, last, label⟩ ⟨first, agent⟩ ⟨last, target⟩ ↔
      ActIPO rules (K.context label) agent target := by
  constructor
  · intro firing
    cases firing with
    | actual _ _ _ actual => exact actual
  · exact Step.actual label agent target

inductive Formula : Index → Type (max uIndex uLabel) where
  | top {interface} : Formula interface
  | conj {interface} (first second : Formula interface) : Formula interface
  | neg {interface} (inner : Formula interface) : Formula interface
  | diamond {first last} (label : K.Label first last) (inner : Formula last) : Formula first

def Formula.depth : {interface : Index} → Formula K interface → Nat
  | _, .top => 0
  | _, .conj first second => max first.depth second.depth
  | _, .neg inner => inner.depth
  | _, .diamond _ inner => inner.depth + 1

def Holds : {interface : Index} → Formula K interface → (origin ⟶ K.object interface) → Prop
  | _, .top, _ => True
  | _, .conj first second, agent => Holds first agent ∧ Holds second agent
  | _, .neg inner, agent => ¬ Holds inner agent
  | _, .diamond label inner, agent =>
      ∃ target, ActIPO rules (K.context label) agent target ∧ Holds inner target

def Formula.erase : {interface : Index} → Formula K interface →
    HennessyMilner.Formula Index (TotalLabel K)
  | _, .top => .top
  | _, .conj first second => .conj first.erase second.erase
  | _, .neg inner => .neg inner.erase
  | first, .diamond (last := last) label inner => .dia ⟨first, last, label⟩ inner.erase

theorem erase_depth {interface : Index} (formula : Formula K interface) :
    formula.erase.depth = formula.depth := by
  induction formula with
  | top => rfl
  | conj first second firstRead secondRead =>
      change max first.erase.depth second.erase.depth = max first.depth second.depth
      rw [firstRead, secondRead]
  | neg inner inductionHypothesis => exact inductionHypothesis
  | diamond label inner inductionHypothesis =>
      exact congrArg (· + 1) inductionHypothesis

theorem erase_satisfaction {interface : Index} (formula : Formula K interface) :
    ∀ agent : origin ⟶ K.object interface,
      (system K origin rules).sat formula.erase ⟨interface, agent⟩ ↔ Holds K origin rules formula agent := by
  induction formula with
  | top => intro agent; exact Iff.rfl
  | conj first second firstRead secondRead =>
      intro agent
      exact and_congr (firstRead agent) (secondRead agent)
  | neg inner inductionHypothesis => intro agent; exact not_congr (inductionHypothesis agent)
  | diamond label inner inductionHypothesis =>
      intro agent
      constructor
      · rintro ⟨target, firing, held⟩
        cases firing with
        | actual label agent target firing =>
            exact ⟨target, firing, (inductionHypothesis target).mp held⟩
      · rintro ⟨target, firing, held⟩
        exact ⟨⟨_, target⟩, Step.actual label agent target firing,
          (inductionHypothesis target).mpr held⟩

end Mettapedia.GSLT.InterfaceObservationKit
