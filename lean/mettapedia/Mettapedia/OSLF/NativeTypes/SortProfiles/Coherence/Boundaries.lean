import Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.Formation

open Mettapedia.OSLF.Framework

/-!
# Separation of context coherence and uniform sort invariance

Simultaneous formation uses the chosen shared context of a displayed law.
Invariance over every sort valuation is a stronger and different obligation.
The variable equation below has a coherent context but fails the uniform
obligation, so one center cannot silently be advertised as the other.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence

open Mettapedia.UniversalAlgebra
open Mettapedia.OSLF.Framework.ModalHypercube (HSort)

variable {S : Signature.{0}}

def UniformSortInvariant (profile : Profile S) (equation : Equation S) : Prop :=
  ∀ valuation : Nat → HSort,
    equation.1.evaluate (partialModel profile) (fun index => some (valuation index)) =
      equation.2.evaluate (partialModel profile) (fun index => some (valuation index))

/-- A context can form both variables at the same sort without making the
sort interpretations of arbitrary valuations equal. -/
theorem shared_context_is_not_uniform_stability (profile : Profile S) :
    CoherentEquation profile (.var 0, .var 1) ∧
      ¬ UniformSortInvariant profile (.var 0, .var 1) := by
  constructor
  · exact ⟨fun _ => .star, .star, .variableTerm 0, .variableTerm 1⟩
  · intro invariant
    have different := invariant (fun index => if index = 0 then .star else .box)
    simp only [Term.evaluate, Nat.one_ne_zero, ↓reduceIte, Option.some.injEq] at different
    cases different

/-- The common context and every typing witness survive admitted typed
substitutions; an untyped substitution receives no such claim. -/
theorem admitted_substitution_preserves_both_sides (profile : Profile S) (equation : Equation S)
    (valuation target : Nat → HSort) (sort : HSort)
    (left : Formed profile valuation equation.1 sort)
    (right : Formed profile valuation equation.2 sort)
    (substitution : Nat → Term S)
    (typed : ∀ index, Formed profile target (substitution index) (valuation index)) :
    CoherentEquation profile
      (equation.1.subst substitution, equation.2.subst substitution) :=
  ⟨target, sort, left.substitute substitution typed, right.substitute substitution typed⟩

end Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence
