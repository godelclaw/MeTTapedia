import Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.Stability

open Mettapedia.OSLF.Framework

/-!
# Typed substitution of stable profile laws

The relation is preserved for substitutions that actually satisfy the shared
context valuation. Both code formation and rejection are retained. No claim
is made for replacements with an unproved typing judgment.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence

open Mettapedia.UniversalAlgebra
open Mettapedia.OSLF.Framework.ModalHypercube (HSort)

variable {S : Signature.{0}}

theorem evaluate_typed_substitution (profile : Profile S) (term : Term S)
    (source target : Nat → HSort) (substitution : Nat → Term S)
    (typed : ∀ index, Formed profile target (substitution index) (source index)) :
    (term.subst substitution).evaluate (partialModel profile) (fun index => some (target index)) =
      term.evaluate (partialModel profile) (fun index => some (source index)) := by
  rw [Term.evaluate_subst]
  apply congrArg (term.evaluate (partialModel profile))
  funext index
  exact formed_evaluate (typed index)

/-- An actual admitted substitution preserves the equation's formation
comparison, including the specified common result sort. -/
theorem stable_typed_substitution {profile : Profile S} {equation : Equation S}
    (stable : StableEquation profile equation) (source target : Nat → HSort)
    (substitution : Nat → Term S)
    (typed : ∀ index, Formed profile target (substitution index) (source index)) (sort : HSort) :
    Formed profile target (equation.1.subst substitution) sort ↔
      Formed profile target (equation.2.subst substitution) sort := by
  rw [← evaluate_iff_formed, ← evaluate_iff_formed,
    evaluate_typed_substitution profile equation.1 source target substitution typed,
    evaluate_typed_substitution profile equation.2 source target substitution typed,
    evaluate_iff_formed, evaluate_iff_formed]
  exact stable.2 source sort

end Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence
