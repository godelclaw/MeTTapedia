import Mettapedia.Logic.HOL.GuardedRetraction
import Mettapedia.Logic.HOL.BooleanFacts
import Mettapedia.Logic.HOL.Semantics.ModelPropertySoundness

/-!
# A nonempty guarded domain and failure of unguarded reflection

The existing standard Boolean model validates the retraction of a collapsing
map on its false-only guard. That guard has a valid value. Removing the two
validity premises then reflects an equality between the encoded true/false
values into a false source equality. The functional-embedding proof provides
a separate positive representation that separates both Boolean values.
-/

set_option autoImplicit false
namespace Mettapedia.Logic.HOL.GuardedRetraction.Controls

abbrev Const := BooleanFacts.Const
abbrev boolean : Ty BooleanFacts.Base := .prop

def collapse : ClosedTerm Const (boolean ⇒ boolean) := .lam .bot
def falseOnly : ClosedTerm Const (boolean ⇒ .prop) := .lam (.not (.var .vz))
def model := BooleanFacts.model (ULift.{1} Bool)

def unguarded : ClosedFormula Const :=
  unguardedConsequence collapse collapse falseOnly .top .bot

theorem guarded_law_valid : model.models (law collapse collapse falseOnly) := by
  change ∀ value : ULift.{1} Prop, True → (¬ value.down) → (False ↔ value.down)
  intro value _ valid
  exact ⟨False.elim, valid⟩

theorem guard_inhabited : model.models (.app falseOnly .bot) := not_false

theorem true_outside_guard : ¬ model.models (.app falseOnly .top) := by
  change ¬ ¬ True
  exact fun rejected => rejected trivial

theorem unguarded_invalid : ¬ model.models unguarded := by
  intro claimed
  have contradiction : True ↔ False := claimed guarded_law_valid Iff.rfl
  exact contradiction.mp trivial

theorem unguarded_not_derivable : ¬ ExtDerivation.Theorem Const unguarded := by
  intro proof
  exact unguarded_invalid (Soundness.extTheorem_sound_of_fullDomains proof model (fun _ _ => trivial))

theorem functional_separation_derivable : ExtDerivation.Theorem Const
    (.not (.eq (.app (constantEmbedding (σ := boolean)) .top) (.app constantEmbedding .bot))) :=
  (functionalSeparation (Const := Const) (Γ := [])).erase

#print axioms guarded_law_valid
#print axioms guard_inhabited
#print axioms unguarded_invalid
#print axioms unguarded_not_derivable
#print axioms functional_separation_derivable
end Mettapedia.Logic.HOL.GuardedRetraction.Controls
