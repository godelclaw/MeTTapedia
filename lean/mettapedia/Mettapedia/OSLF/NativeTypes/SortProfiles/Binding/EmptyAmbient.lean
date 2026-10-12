import Mettapedia.OSLF.Syntax.IntrinsicScopedConditionalSubstitution

open Mettapedia.OSLF.Framework

/-!
# Closing the captured context of a binding schema

An empty captured context has no extra semantic inputs. Its complete
contextual interpretation agrees with the ordinary dependency interpretation
after the supplied ordinary substitution. The comparison follows every
operator argument beneath its own declared binders.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.SortProfiles.Binding.EmptyAmbient

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FreeBindingTerms
open Mettapedia.OSLF.Binding.BindingSubstitutionAlgebra
open Mettapedia.OSLF.Binding.BindingEquationalModels
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalSubstitution

universe u

variable {S : Signature} {M : List (MetaArity S)}

def emptyEnvironment (A : BindingCloneAlgebra.Algebra.{u} S) {target : Ctx S} :
    Environment S A.substitution.Carrier [] target :=
  fun _ impossible => nomatch impossible

theorem empty_environment_unique (A : BindingCloneAlgebra.Algebra.{u} S)
    {target : Ctx S} (environment : Environment S A.substitution.Carrier [] target) :
    environment = emptyEnvironment A := by
  funext sort impossible
  nomatch impossible

theorem empty_environment_identity (A : BindingCloneAlgebra.Algebra.{u} S) :
    emptyEnvironment A (target := []) =
      (fun _ position => A.substitution.injectVar position) :=
  (empty_environment_unique A _).symm

theorem empty_environment_weaken (A : BindingCloneAlgebra.Algebra.{u} S)
    {target : Ctx S} (binders : Ctx S) :
    SemanticContextualMetavariables.weakenEnvironment A binders
        (emptyEnvironment A (target := target)) = emptyEnvironment A :=
  empty_environment_unique A _

def dependencyValue (A : BindingCloneAlgebra.Algebra.{u} S)
    {dependencies : Ctx S} {sort : S.Srt}
    (body : A.substitution.Carrier (dependencies ++ []) sort) :
    A.substitution.Carrier dependencies sort :=
  A.substitution.substitute
    (SemanticContextualMetavariables.joinEnvironment
      (fun _ position => A.substitution.injectVar position) (emptyEnvironment A)) body

def dependencyValuation (A : BindingCloneAlgebra.Algebra.{u} S)
    (body : SemanticContextualMetavariables.Valuation (M := M) A []) : MetaValuation A M :=
  fun index => dependencyValue A (body index)

theorem apply_empty_ambient (A : BindingCloneAlgebra.Algebra.{u} S)
    {dependencies target : Ctx S} {sort : S.Srt}
    (body : A.substitution.Carrier (dependencies ++ []) sort)
    (arguments : Environment S A.substitution.Carrier dependencies target) :
    SemanticContextualMetavariables.apply A body arguments (emptyEnvironment A) =
      A.substitution.substitute arguments (dependencyValue A body) := by
  unfold SemanticContextualMetavariables.apply dependencyValue
  rw [A.substitution.substitute_comp]
  congr 1
  funext type position
  rw [substitute_joinEnvironment A.substitution arguments dependencies]
  have projectedArguments :
      (fun type position => A.substitution.substitute arguments
        (A.substitution.injectVar position : A.substitution.Carrier dependencies type)) = arguments := by
    funext type position
    exact A.substitution.substitute_var arguments position
  have emptyAfter :
      (fun type position => A.substitution.substitute arguments
        (emptyEnvironment A type position)) = emptyEnvironment A := empty_environment_unique A _
  rw [projectedArguments, emptyAfter]

mutual

theorem interpretation_empty_ambient (A : BindingCloneAlgebra.Algebra.{u} S)
    {source target : Ctx S}
    (body : SemanticContextualMetavariables.Valuation (M := M) A [])
    (ordinary : Environment S A.substitution.Carrier source target) :
    ∀ {sort : S.Srt} (term : Term (withMetas S M) source sort),
      SemanticContextualMetavariables.interpretSchema A body (emptyEnvironment A) ordinary term =
        A.substitution.substitute ordinary
          (BindingEquationInterpretation.interpretSchema A (dependencyValuation A body) term)
  | _, .var position => (A.substitution.substitute_var ordinary position).symm
  | _, .op (.inl op) arguments => by
      change A.operation op
          (SemanticContextualMetavariables.interpretArgs A body (emptyEnvironment A) ordinary arguments) =
        A.substitution.substitute ordinary
          (A.operation op (BindingEquationInterpretation.interpretSchemaArgs A
            (dependencyValuation A body) arguments))
      rw [A.operation_substitute, arguments_empty_ambient]
  | _, .op (.inr (.mk index)) arguments => by
      change SemanticContextualMetavariables.apply A (body index)
          (argsEnvironment A (SemanticContextualMetavariables.interpretArgs A body
            (emptyEnvironment A) ordinary arguments)) (emptyEnvironment A) =
        A.substitution.substitute ordinary
          (applyMeta A (dependencyValuation A body index)
            (BindingEquationInterpretation.interpretSchemaArgs A (dependencyValuation A body) arguments))
      rw [applyMeta_substitute, apply_empty_ambient, arguments_empty_ambient]
      rfl
termination_by _ term => 2 * termSize term
decreasing_by
  all_goals simp only [termSize]
  all_goals omega

theorem arguments_empty_ambient (A : BindingCloneAlgebra.Algebra.{u} S)
    {source target : Ctx S}
    (body : SemanticContextualMetavariables.Valuation (M := M) A [])
    (ordinary : Environment S A.substitution.Carrier source target) :
    ∀ {arity : List (List S.Srt × S.Srt)} (arguments : Args (withMetas S M) arity source),
      SemanticContextualMetavariables.interpretArgs A body (emptyEnvironment A) ordinary arguments =
        A.substitution.substituteArgs ordinary
          (BindingEquationInterpretation.interpretSchemaArgs A (dependencyValuation A body) arguments)
  | _, .nil => rfl
  | _, .cons (bs := binders) head tail => by
      change FamilyArgs.cons
          (SemanticContextualMetavariables.interpretSchema A body
            (SemanticContextualMetavariables.weakenEnvironment A binders (emptyEnvironment A))
            (A.substitution.liftEnvironment ordinary binders) head)
          (SemanticContextualMetavariables.interpretArgs A body (emptyEnvironment A) ordinary tail) =
        FamilyArgs.cons
          (A.substitution.substitute (A.substitution.liftEnvironment ordinary binders)
            (BindingEquationInterpretation.interpretSchema A (dependencyValuation A body) head))
          (A.substitution.substituteArgs ordinary
            (BindingEquationInterpretation.interpretSchemaArgs A (dependencyValuation A body) tail))
      rw [empty_environment_weaken, interpretation_empty_ambient, arguments_empty_ambient]
termination_by _ arguments => 2 * argsSize arguments + 1
decreasing_by
  all_goals simp only [argsSize]
  all_goals first | omega | have := termSize_pos head; omega

end

theorem close_captured_context (A : BindingCloneAlgebra.Algebra.{u} S)
    {captured source : Ctx S}
    (body : SemanticContextualMetavariables.Valuation (M := M) A captured)
    (ambient : Environment S A.substitution.Carrier captured [])
    (ordinary : Environment S A.substitution.Carrier source [])
    {sort : S.Srt} (term : Term (withMetas S M) source sort) :
    SemanticContextualMetavariables.interpretSchema A body ambient ordinary term =
      A.substitution.substitute ordinary
        (BindingEquationInterpretation.interpretSchema A
          (dependencyValuation A (substValuation A ambient body)) term) := by
  have composed :
      (fun type position => A.substitution.substitute (emptyEnvironment A)
        (ambient type position)) = ambient := by
    rw [empty_environment_identity]
    funext type position
    exact A.substitution.substitute_identity (ambient type position)
  have moved := interpretSchema_postAmbient A (emptyEnvironment A) ambient body ordinary term
  rw [composed] at moved
  exact moved.trans (interpretation_empty_ambient A _ ordinary term)

end Mettapedia.OSLF.NativeTypes.SortProfiles.Binding.EmptyAmbient
