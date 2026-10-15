import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeMonotoneSyntax
import Mettapedia.OSLF.NativeTypes.Generation.NativeGraphFormation

/-!
# Ordinary formation for higher-order native operators and fixed-point formulas

The emitted formulas use only the existing dependent native grammar. Each
formation witness is built from the actual authored context, type, operator
and argument derivations using its ordinary rule trees.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeMonotoneFormation

open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open Mettapedia.OSLF.NativeTypes.Generation
open FixedPointSyntax NativeMonotoneSyntax

universe u
variable {S : Symbols.{u}} {D : Signature S} {n : Nat}

def extendContext (context : ContextExpr S n) (domain : TypeExpr S n)
    (formed : Derivation D (.context context))
    (domainFormed : Derivation D (.type context domain)) :
    Derivation D (.context (.snoc context domain)) :=
  deriveList (.contextExtend context domain) (.cons formed (.cons domainFormed .nil))


def applicationTyping (context : ContextExpr S n) (domain : TypeExpr S n)
    (function argument : TermExpr S n) (formed : Derivation D (.context context))
    (domainFormed : Derivation D (.type context domain))
    (functionTyped : Derivation D (.term context function (predicateType domain)))
    (argumentTyped : Derivation D (.term context argument domain)) :
    Derivation D (.term context (.app domain .propositions function argument) .propositions) :=
  deriveList (.application context domain .propositions function argument)
    (.cons domainFormed (.cons
      (deriveList (.propositionType (.snoc context domain))
        (.cons (extendContext context domain formed domainFormed) .nil))
      (.cons functionTyped (.cons argumentTyped .nil))))


def applicationFormation (context : ContextExpr S n) (domain : TypeExpr S n)
    (function argument : TermExpr S n) (formed : Derivation D (.context context))
    (domainFormed : Derivation D (.type context domain))
    (functionTyped : Derivation D (.term context function (predicateType domain)))
    (argumentTyped : Derivation D (.term context argument domain)) :
    Derivation D (.predicate context (application domain function argument)) :=
  deriveList (.holdsFormation context (.app domain .propositions function argument))
    (.cons (applicationTyping context domain function argument formed domainFormed
      functionTyped argumentTyped) .nil)


def inclusionFormation (context : ContextExpr S n) (domain : TypeExpr S n)
    (first second : TermExpr S n) (formed : Derivation D (.context context))
    (domainFormed : Derivation D (.type context domain))
    (firstTyped : Derivation D (.term context first (predicateType domain)))
    (secondTyped : Derivation D (.term context second (predicateType domain))) :
    Derivation D (.predicate context (inclusion domain first second)) := by
  let extended := extendContext context domain formed domainFormed
  let weakenedDomain := NativeEquality.weakenType context domain domain domainFormed domainFormed
  have variableTyped : Derivation D (.term (.snoc context domain) (.var 0) (domain.rename Fin.succ)) := by
    simpa only [RuleCode.conclusion, ContextExpr.lookup_zero] using
      deriveList (.variable (.snoc context domain) 0) (.cons extended .nil)
  have firstWeakened : Derivation D (.term (.snoc context domain) (first.rename Fin.succ)
      (predicateType (domain.rename Fin.succ))) := by
    simpa only [predicateType, NativeEquality.predicateType, TypeExpr.rename] using
      NativeEquality.weakenTerm context domain (predicateType domain) first domainFormed firstTyped
  have secondWeakened : Derivation D (.term (.snoc context domain) (second.rename Fin.succ)
      (predicateType (domain.rename Fin.succ))) := by
    simpa only [predicateType, NativeEquality.predicateType, TypeExpr.rename] using
      NativeEquality.weakenTerm context domain (predicateType domain) second domainFormed secondTyped
  exact deriveList (.universalFormation context domain _)
    (.cons domainFormed (.cons
      (deriveList (.implicationFormation (.snoc context domain) _ _)
        (.cons (applicationFormation _ _ _ _ extended weakenedDomain firstWeakened variableTyped)
          (.cons (applicationFormation _ _ _ _ extended weakenedDomain secondWeakened variableTyped) .nil))) .nil))


def operatorApplicationTyping (context : ContextExpr S n) (domain : TypeExpr S n)
    (operator candidate : TermExpr S n) (formed : Derivation D (.context context))
    (domainFormed : Derivation D (.type context domain))
    (operatorTyped : Derivation D (.term context operator (operatorType domain)))
    (candidateTyped : Derivation D (.term context candidate (predicateType domain))) :
    Derivation D (.term context (applyOperator domain operator candidate) (predicateType domain)) := by
  let predicates := NativeEquality.predicateFormation context domain formed domainFormed
  simpa only [RuleCode.conclusion, TypeExpr.instantiate_weaken, applyOperator] using
    deriveList (.application context (predicateType domain)
      ((predicateType domain).rename Fin.succ) operator candidate)
      (.cons predicates (.cons
        (NativeEquality.weakenType context (predicateType domain) (predicateType domain)
          predicates predicates) (.cons operatorTyped (.cons candidateTyped .nil))))


def inclusionCongruence (context : ContextExpr S n) (domain : TypeExpr S n)
    (first first' second second' : TermExpr S n)
    (formed : Derivation D (.context context))
    (domainFormed : Derivation D (.type context domain))
    (firstEquality : Derivation D (.termEq context first first' (predicateType domain)))
    (secondEquality : Derivation D (.termEq context second second' (predicateType domain)))
    (firstTyped : Derivation D (.term context first' (predicateType domain)))
    (secondTyped : Derivation D (.term context second' (predicateType domain))) :
    Derivation D (.predicateEq context (inclusion domain first second)
      (inclusion domain first' second')) := by
  let extended := extendContext context domain formed domainFormed
  let weakenedDomain := NativeEquality.weakenType context domain domain domainFormed domainFormed
  let weakening := deriveList (.substitutionWeaken context domain) (.cons domainFormed .nil)
  have variableTyped : Derivation D (.term (.snoc context domain) (.var 0) (domain.rename Fin.succ)) := by
    simpa only [RuleCode.conclusion, ContextExpr.lookup_zero] using
      deriveList (.variable (.snoc context domain) 0) (.cons extended .nil)
  let variableEquality := deriveList
    (.termReflexivity (.snoc context domain) (.var 0) (domain.rename Fin.succ))
    (.cons variableTyped .nil)
  have firstWeakened : Derivation D (.termEq (.snoc context domain)
      (first.rename Fin.succ) (first'.rename Fin.succ) (predicateType (domain.rename Fin.succ))) := by
    simpa only [RuleCode.conclusion, TermExpr.substitute_variables,
      TypeExpr.substitute_variables, predicateType, NativeEquality.predicateType, TypeExpr.rename] using
      deriveList (.substituteTermEquality (.snoc context domain) context (fun i => .var i.succ)
        first first' (predicateType domain)) (.cons weakening (.cons firstEquality .nil))
  have secondWeakened : Derivation D (.termEq (.snoc context domain)
      (second.rename Fin.succ) (second'.rename Fin.succ) (predicateType (domain.rename Fin.succ))) := by
    simpa only [RuleCode.conclusion, TermExpr.substitute_variables,
      TypeExpr.substitute_variables, predicateType, NativeEquality.predicateType, TypeExpr.rename] using
      deriveList (.substituteTermEquality (.snoc context domain) context (fun i => .var i.succ)
        second second' (predicateType domain)) (.cons weakening (.cons secondEquality .nil))
  let propositions := deriveList
    (.propositionType (.snoc (.snoc context domain) (domain.rename Fin.succ)))
    (.cons (extendContext _ _ extended weakenedDomain) .nil)
  let firstApplication := deriveList
    (.applicationCongruence (.snoc context domain) (domain.rename Fin.succ) .propositions
      (first.rename Fin.succ) (first'.rename Fin.succ) (.var 0) (.var 0))
    (.cons weakenedDomain (.cons propositions (.cons firstWeakened (.cons variableEquality .nil))))
  let secondApplication := deriveList
    (.applicationCongruence (.snoc context domain) (domain.rename Fin.succ) .propositions
      (second.rename Fin.succ) (second'.rename Fin.succ) (.var 0) (.var 0))
    (.cons weakenedDomain (.cons propositions (.cons secondWeakened (.cons variableEquality .nil))))
  let firstHolds := deriveList (.holdsCongruence _ _ _) (.cons firstApplication .nil)
  let secondHolds := deriveList (.holdsCongruence _ _ _) (.cons secondApplication .nil)
  let bodyEquality := deriveList (.implicationCongruence _ _ _ _ _)
    (.cons firstHolds (.cons secondHolds .nil))
  have bodyFormed : Derivation D (.predicate (.snoc context domain)
      (.implies (application (domain.rename Fin.succ) (first'.rename Fin.succ) (.var 0))
        (application (domain.rename Fin.succ) (second'.rename Fin.succ) (.var 0)))) := by
    have firstWeakenedTyped : Derivation D (.term (.snoc context domain) (first'.rename Fin.succ)
        (predicateType (domain.rename Fin.succ))) := by
      simpa only [predicateType, NativeEquality.predicateType, TypeExpr.rename] using
        NativeEquality.weakenTerm context domain (predicateType domain) first' domainFormed firstTyped
    have secondWeakenedTyped : Derivation D (.term (.snoc context domain) (second'.rename Fin.succ)
        (predicateType (domain.rename Fin.succ))) := by
      simpa only [predicateType, NativeEquality.predicateType, TypeExpr.rename] using
        NativeEquality.weakenTerm context domain (predicateType domain) second' domainFormed secondTyped
    exact deriveList (.implicationFormation _ _ _)
      (.cons (applicationFormation _ _ _ _ extended weakenedDomain firstWeakenedTyped variableTyped)
        (.cons (applicationFormation _ _ _ _ extended weakenedDomain secondWeakenedTyped variableTyped) .nil))
  exact deriveList (.universalCongruence context domain domain _ _)
    (.cons (deriveList (.typeReflexivity context domain) (.cons domainFormed .nil))
      (.cons bodyEquality (.cons bodyFormed .nil)))


theorem operatorType_rename {m : Nat} (mapping : Renaming n m) (domain : TypeExpr S n) :
    (operatorType domain).rename mapping = operatorType (domain.rename mapping) := by
  simp only [operatorType, predicateType, TypeExpr.rename]
  rw [TypeExpr.rename_comp, TypeExpr.rename_comp]
  rfl

def operatorTypeFormation (context : ContextExpr S n) (domain : TypeExpr S n)
    (formed : Derivation D (.context context))
    (domainFormed : Derivation D (.type context domain)) :
    Derivation D (.type context (operatorType domain)) := by
  let predicates := NativeEquality.predicateFormation context domain formed domainFormed
  exact deriveList (.piFormation context (predicateType domain) ((predicateType domain).rename Fin.succ))
    (.cons predicates (.cons
      (NativeEquality.weakenType context (predicateType domain) (predicateType domain) predicates predicates) .nil))

def operatorWeaken (context : ContextExpr S n) (binder domain : TypeExpr S n)
    (operator : TermExpr S n) (binderFormed : Derivation D (.type context binder))
    (operatorTyped : Derivation D (.term context operator (operatorType domain))) :
    Derivation D (.term (.snoc context binder) (operator.rename Fin.succ)
      (operatorType (domain.rename Fin.succ))) := by
  simpa only [operatorType_rename] using
    NativeEquality.weakenTerm context binder (operatorType domain) operator binderFormed operatorTyped

def candidateTyped (context : ContextExpr S n) (domain : TypeExpr S n)
    (formed : Derivation D (.context context))
    (domainFormed : Derivation D (.type context domain)) :
    Derivation D (.term (.snoc context (predicateType domain)) (.var 0)
      (predicateType (domain.rename Fin.succ))) := by
  let predicates := NativeEquality.predicateFormation context domain formed domainFormed
  simpa only [RuleCode.conclusion, ContextExpr.lookup_zero, predicateType, TypeExpr.rename] using
    deriveList (.variable (.snoc context (predicateType domain)) 0)
      (.cons (extendContext context (predicateType domain) formed predicates) .nil)

def prefixedFormation (context : ContextExpr S n) (domain : TypeExpr S n) (operator : TermExpr S n)
    (formed : Derivation D (.context context))
    (domainFormed : Derivation D (.type context domain))
    (operatorTyped : Derivation D (.term context operator (operatorType domain))) :
    Derivation D (.predicate (.snoc context (predicateType domain))
      (NativeMonotoneSyntax.prefixed domain operator)) := by
  let predicates := NativeEquality.predicateFormation context domain formed domainFormed
  let extended := extendContext context (predicateType domain) formed predicates
  let weakenedDomain := NativeEquality.weakenType context (predicateType domain) domain predicates domainFormed
  let variableTyped := candidateTyped context domain formed domainFormed
  let application := operatorApplicationTyping _ _ _ _ extended weakenedDomain
    (operatorWeaken context (predicateType domain) domain operator predicates operatorTyped) variableTyped
  exact inclusionFormation _ _ _ _ extended weakenedDomain application variableTyped

def postfixedFormation (context : ContextExpr S n) (domain : TypeExpr S n) (operator : TermExpr S n)
    (formed : Derivation D (.context context))
    (domainFormed : Derivation D (.type context domain))
    (operatorTyped : Derivation D (.term context operator (operatorType domain))) :
    Derivation D (.predicate (.snoc context (predicateType domain))
      (NativeMonotoneSyntax.postfixed domain operator)) := by
  let predicates := NativeEquality.predicateFormation context domain formed domainFormed
  let extended := extendContext context (predicateType domain) formed predicates
  let weakenedDomain := NativeEquality.weakenType context (predicateType domain) domain predicates domainFormed
  let variableTyped := candidateTyped context domain formed domainFormed
  let application := operatorApplicationTyping _ _ _ _ extended weakenedDomain
    (operatorWeaken context (predicateType domain) domain operator predicates operatorTyped) variableTyped
  exact inclusionFormation _ _ _ _ extended weakenedDomain variableTyped application

def argumentUnderPredicate (context : ContextExpr S n) (domain : TypeExpr S n)
    (tested : TermExpr S n) (formed : Derivation D (.context context))
    (domainFormed : Derivation D (.type context domain))
    (testedTyped : Derivation D (.term context tested domain)) :
    Derivation D (.predicate (.snoc context (predicateType domain))
      (application (domain.rename Fin.succ) (.var 0) (tested.rename Fin.succ))) := by
  let predicates := NativeEquality.predicateFormation context domain formed domainFormed
  let extended := extendContext context (predicateType domain) formed predicates
  let weakenedDomain := NativeEquality.weakenType context (predicateType domain) domain predicates domainFormed
  exact applicationFormation _ _ _ _ extended weakenedDomain
    (candidateTyped context domain formed domainFormed)
    (NativeEquality.weakenTerm context (predicateType domain) domain tested predicates testedTyped)

def leastFormation (context : ContextExpr S n) (domain : TypeExpr S n)
    (operator tested : TermExpr S n) (formed : Derivation D (.context context))
    (domainFormed : Derivation D (.type context domain))
    (operatorTyped : Derivation D (.term context operator (operatorType domain)))
    (testedTyped : Derivation D (.term context tested domain)) :
    Derivation D (.predicate context (NativeMonotoneSyntax.least domain operator tested)) :=
  deriveList (.universalFormation context (predicateType domain) _)
    (.cons (NativeEquality.predicateFormation context domain formed domainFormed)
      (.cons (deriveList (.implicationFormation _ _ _)
        (.cons (prefixedFormation context domain operator formed domainFormed operatorTyped)
          (.cons (argumentUnderPredicate context domain tested formed domainFormed testedTyped) .nil))) .nil))

def greatestFormation (context : ContextExpr S n) (domain : TypeExpr S n)
    (operator tested : TermExpr S n) (formed : Derivation D (.context context))
    (domainFormed : Derivation D (.type context domain))
    (operatorTyped : Derivation D (.term context operator (operatorType domain)))
    (testedTyped : Derivation D (.term context tested domain)) :
    Derivation D (.predicate context (NativeMonotoneSyntax.greatest domain operator tested)) :=
  deriveList (.existentialFormation context (predicateType domain) _)
    (.cons (NativeEquality.predicateFormation context domain formed domainFormed)
      (.cons (deriveList (.conjunctionFormation _ _ _)
        (.cons (postfixedFormation context domain operator formed domainFormed operatorTyped)
          (.cons (argumentUnderPredicate context domain tested formed domainFormed testedTyped) .nil))) .nil))

variable [DecidableEq S.TypeSymbol] [DecidableEq S.TermSymbol] [DecidableEq S.PredicateSymbol]

theorem leastFormation_checked (context : ContextExpr S n) (domain : TypeExpr S n)
    (operator tested : TermExpr S n) (formed : Derivation D (.context context))
    (domainFormed : Derivation D (.type context domain))
    (operatorTyped : Derivation D (.term context operator (operatorType domain)))
    (testedTyped : Derivation D (.term context tested domain)) :
    Certificates.Refinement.check
      (Certificates.Refinement.erase
        (leastFormation context domain operator tested formed domainFormed operatorTyped testedTyped))
      (.predicate context (NativeMonotoneSyntax.least domain operator tested)) = true :=
  Certificates.Refinement.check_erase _

theorem greatestFormation_checked (context : ContextExpr S n) (domain : TypeExpr S n)
    (operator tested : TermExpr S n) (formed : Derivation D (.context context))
    (domainFormed : Derivation D (.type context domain))
    (operatorTyped : Derivation D (.term context operator (operatorType domain)))
    (testedTyped : Derivation D (.term context tested domain)) :
    Certificates.Refinement.check
      (Certificates.Refinement.erase
        (greatestFormation context domain operator tested formed domainFormed operatorTyped testedTyped))
      (.predicate context (NativeMonotoneSyntax.greatest domain operator tested)) = true :=
  Certificates.Refinement.check_erase _

end Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeMonotoneFormation
