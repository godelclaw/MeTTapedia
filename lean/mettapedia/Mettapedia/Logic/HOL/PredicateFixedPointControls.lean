import Mettapedia.Logic.HOL.PredicateFixedPoint
import Mettapedia.Logic.HOL.Semantics.ModelPropertySoundness

/-!
# Reachable and unreachable points, and a non-monotone operator

A seed at zero and one transition from zero to one give a nontrivial least
closure on a three-element carrier. The third point remains outside it.
Complement reverses predicate inclusion and has no fixed point; its model
therefore refutes dropping the monotonicity premise from the logical schema.
-/

set_option autoImplicit false
namespace Mettapedia.Logic.HOL.PredicateFixedPoint.Controls
abbrev carrier : Ty Unit := .base ()
inductive Const : Ty Unit → Type where
  | seed : Const (Predicate carrier)
  | edge : Const (carrier ⇒ carrier ⇒ .prop)

def model : HenkinModel.{0, 0, 0} Unit Const :=
  .standard (fun _ => ULift.{1} (Fin 3)) (fun symbol => match symbol with
    | .seed => fun point => .up (point.down = 0)
    | .edge => fun first second => .up (first.down = 0 ∧ second.down = 1))

def emptyValuation : model.Valuation [] := fun impossible => nomatch impossible

def successorOperator : ClosedTerm Const (Operator carrier) :=
  .lam (.lam (.or (.app (.const .seed) (.var .vz))
    (.ex (.and (.app (.var (.vs (.vs .vz))) (.var .vz))
      (.app (.app (.const .edge) (.var .vz)) (.var (.vs .vz)))))))

def complement : ClosedTerm Const (Operator carrier) :=
  .lam (.lam (.not (.app (.var (.vs .vz)) (.var .vz))))

def member (point : Fin 3) : Prop :=
  (model.denote (least successorOperator) emptyValuation (.up point)).down

theorem successor_monotone : model.models (monotone successorOperator) := by
  intro first _ second _ inclusion point _ present
  rcases present with seed | ⟨previous, admitted, inside, edge⟩
  · exact .inl seed
  · exact .inr ⟨previous, admitted, inclusion previous admitted inside, edge⟩

theorem zero_member : member 0 := by
  intro property _ closed
  exact closed (.up 0) trivial (.inl rfl)

theorem one_member : member 1 := by
  intro property admitted closed
  exact closed (.up 1) trivial (.inr ⟨.up 0, trivial, zero_member property admitted closed, rfl, rfl⟩)

theorem two_not_member : ¬ member 2 := by
  intro closure
  have excluded := closure (fun point => .up (point.down ≠ 2)) trivial (by
    intro point _ present
    rcases present with seed | ⟨previous, _, _, edge⟩
    · change point.down = 0 at seed
      change point.down ≠ 2
      rw [seed]
      decide +kernel
    · change previous.down = 0 ∧ point.down = 1 at edge
      change point.down ≠ 2
      rw [edge.2]
      decide +kernel)
  exact excluded rfl

theorem complement_not_monotone : ¬ model.models (monotone complement) := by
  intro order
  have notTrue := order (fun _ => .up False) trivial (fun _ => .up True) trivial
    (fun _ _ impossible => False.elim impossible) (.up 0) trivial (by intro impossible; exact impossible)
  exact notTrue trivial

def unguardedSchema : ClosedFormula Const :=
  .all (equation (.var .vz : Term Const [Operator carrier] (Operator carrier)))

private theorem no_self_negation (p : Prop) (equivalence : p ↔ ¬ p) : False := by
  have negative : ¬ p := fun positive => equivalence.mp positive positive
  exact negative (equivalence.mpr negative)

theorem unguarded_invalid : ¬ model.models unguardedSchema := by
  intro claimed
  have contradiction := claimed (fun property point => .up (¬ (property point).down)) trivial
    (.up 0) trivial
  exact no_self_negation _ contradiction

theorem unguarded_not_derivable : ¬ ExtDerivation.Theorem Const unguardedSchema := by
  intro proof
  exact unguarded_invalid
    (Soundness.extTheorem_sound_of_fullDomains proof model (fun _ _ => trivial))

#print axioms successor_monotone
#print axioms zero_member
#print axioms one_member
#print axioms two_not_member
#print axioms complement_not_monotone
#print axioms unguarded_not_derivable
end Mettapedia.Logic.HOL.PredicateFixedPoint.Controls
