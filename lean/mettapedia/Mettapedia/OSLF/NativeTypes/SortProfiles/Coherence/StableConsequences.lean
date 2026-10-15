import Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.StableSubstitution
import Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.GraphLaws

open Mettapedia.OSLF.Framework

/-!
# Formation-preserving typed display equation consequences

Displayed equations act through actual substitutions satisfying their shared
sort context. One-hole operation contexts and equation detours preserve both
formation and rejection. This is the typed display quotient: a comparison to
the scoped native-pattern quotient still requires the corresponding encoding
and substitution laws.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence

open Mettapedia.UniversalAlgebra
open Mettapedia.OSLF.Framework.ModalHypercube (HSort)

variable {S : Signature.{0}}

/-- Typed equation instances followed by genuine one-hole operation contexts.
The replacement witnesses belong to the formation system itself. -/
inductive TypedDisplayStep (profile : Profile S) (system : EquationSystem S)
    (valuation : Nat → HSort) : Term S → Term S → Prop where
  | equation (law : Equation S) (member : law ∈ system)
      (source : Nat → HSort) (substitution : Nat → Term S)
      (typed : ∀ index, Formed profile valuation (substitution index) (source index)) :
      TypedDisplayStep profile system valuation
        (law.1.subst substitution) (law.2.subst substitution)
  | context (operation : S.Operation) (arguments : Fin (S.arity operation) → Term S)
      (position : Fin (S.arity operation)) {first second : Term S}
      (step : TypedDisplayStep profile system valuation first second) :
      TypedDisplayStep profile system valuation
        (.op operation (Function.update arguments position first))
        (.op operation (Function.update arguments position second))

theorem typed_display_step_formation {profile : Profile S} {system : EquationSystem S}
    (stable : Stable system profile) {valuation : Nat → HSort} {first second : Term S}
    (step : TypedDisplayStep profile system valuation first second) :
    ∀ sort, Formed profile valuation first sort ↔ Formed profile valuation second sort := by
  induction step with
  | equation law member source substitution typed =>
      exact stable_typed_substitution (stable law member) source valuation substitution typed
  | context operation arguments position step ih =>
      intro sort
      rw [formed_operation_iff, formed_operation_iff]
      apply and_congr_right
      intro _
      apply forall_congr'
      intro other
      by_cases same : other = position
      · subst other
        simp only [Function.update_self]
        exact ih _
      · simp only [Function.update_of_ne same]

def TypedDisplayConvertibility (profile : Profile S) (system : EquationSystem S)
    (valuation : Nat → HSort) : Term S → Term S → Prop :=
  Relation.EqvGen (TypedDisplayStep profile system valuation)

theorem typed_display_quotient_formation {profile : Profile S} {system : EquationSystem S}
    (stable : Stable system profile) (valuation : Nat → HSort) (first second : Term S)
    (equivalent : TypedDisplayConvertibility profile system valuation first second) :
    ∀ sort, Formed profile valuation first sort ↔ Formed profile valuation second sort := by
  induction equivalent with
  | rel first second step => exact typed_display_step_formation stable step
  | refl term => intro sort; exact Iff.rfl
  | symm first second _ ih => intro sort; exact (ih sort).symm
  | trans first middle second _ _ left right => intro sort; exact (left sort).trans (right sort)

/-- The executable finite stability test earns contextual and typed
substitution closure, including arbitrary finite equation detours. -/
theorem checked_typed_display_quotient {profile : Profile S} {system : EquationSystem S}
    (checked : checkStable system profile = true) (valuation : Nat → HSort)
    (first second : Term S)
    (equivalent : TypedDisplayConvertibility profile system valuation first second) (sort : HSort) :
    Formed profile valuation first sort ↔ Formed profile valuation second sort :=
  typed_display_quotient_formation ((checkStable_iff system profile).mp checked)
    valuation first second equivalent sort

end Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence
