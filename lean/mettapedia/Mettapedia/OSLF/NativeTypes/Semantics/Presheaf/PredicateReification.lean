import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.FixedPointSyntax
import Mettapedia.GSLT.Topos.NativePowerNativeReadout

/-!
# Predicate Hom/reification in the one native grammar

Reification is ordinary native abstraction of the predicate's quoted
classifier value. It adds no predicate oracle or special application rule.
Actual evaluator readouts earn abstraction, application, and substitution
of the complete native predicate body.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.PredicateReification

open _root_.CategoryTheory Mettapedia.TypeTheory Mettapedia.GSLT.Topos
open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open NativeLocalTypeFormers NativeLocalTypeOperations PresheafNativePropositionReadout
open DisplayedPresheafComprehension

universe u v
variable {S : Symbols.{v}} {C : Type u} [Category.{u} C] {n : Nat}

def reify (domain : TypeExpr S n) (predicate : PropExpr S (n + 1)) : TermExpr S n :=
  .lam domain .propositions (.quote predicate)

theorem reify_rename {m : Nat} (domain : TypeExpr S n) (predicate : PropExpr S (n + 1))
    (mapping : Renaming n m) :
    (reify domain predicate).rename mapping =
      reify (domain.rename mapping) (predicate.rename (liftRenaming mapping)) := rfl

theorem reify_substitute {m : Nat} (domain : TypeExpr S n) (predicate : PropExpr S (n + 1))
    (mapping : Substitution S n m) :
    (reify domain predicate).substitute mapping =
      reify (domain.substitute mapping) (predicate.substitute (liftSubstitution mapping)) := rfl

theorem evaluate_reify (model : ModelData S C) (context : Scope C n)
    (domain : TypeExpr S n) (predicate : PropExpr S (n + 1))
    (A : NativeType context.1) (meaning : Subfunctor (totalSpace A.decoded))
    (domainRead : model.evaluateType context domain = some A)
    (predicateRead : model.evaluatePredicate (context.snoc A) predicate = some meaning) :
    model.evaluateTerm context (reify domain predicate) =
      some ⟨NativeLocalTypeFormers.pi A (nativeOmega (totalSpace A.decoded)),
        NativeLocalTypeOperations.lam (nativeQuote meaning)⟩ :=
  model.evaluate_lambda context domain .propositions A _
    domainRead (model.evaluate_propositions (context.snoc A)) (.quote predicate) _
    (model.evaluate_quote (context.snoc A) predicate meaning predicateRead)

/-- Reified application returns precisely the original predicate pulled
back along the supplied argument's actual dependent section. -/
theorem application_reified {P : Cᵒᵖ ⥤ Type u} (A : NativeType P)
    (meaning : Subfunctor (totalSpace A.decoded)) (argument : A.decoded.sections) :
    nativeHolds (FixedPointSyntax.applicationValue A
      (NativeLocalTypeOperations.lam (nativeQuote meaning)) argument) =
        meaning.preimage (sectionLift A.decoded argument) := by
  rw [FixedPointSyntax.applicationValue_holds]
  unfold NativeLocalTypeOperations.lam
  rw [Equiv.symm_apply_apply, nativeHolds_nativeQuote]

/-- A complete generated reify/app/holds expression uses the original
native evaluator and computes its independent predicate readout. -/
theorem evaluate_reified_application (model : ModelData S C) (context : Scope C n)
    (domain : TypeExpr S n) (predicate : PropExpr S (n + 1)) (argument : TermExpr S n)
    (A : NativeType context.1) (meaning : Subfunctor (totalSpace A.decoded))
    (value : A.decoded.sections)
    (domainRead : model.evaluateType context domain = some A)
    (predicateRead : model.evaluatePredicate (context.snoc A) predicate = some meaning)
    (valueRead : model.evaluateTerm context argument = some ⟨A, value⟩) :
    model.evaluatePredicate context
      (FixedPointSyntax.application domain (reify domain predicate) argument) =
        some (meaning.preimage (sectionLift A.decoded value)) := by
  have readout := FixedPointSyntax.evaluate_application model context domain A
    (reify domain predicate) argument _ value domainRead
    (evaluate_reify model context domain predicate A meaning domainRead predicateRead) valueRead
  rw [application_reified] at readout
  exact readout

end Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.PredicateReification
