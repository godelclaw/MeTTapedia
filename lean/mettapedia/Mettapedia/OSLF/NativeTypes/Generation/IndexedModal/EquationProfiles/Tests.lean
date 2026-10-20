import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.EquationProfiles.Frontier
import Mettapedia.OSLF.StructuralModal.EquationInvariance

/-!
# Executable invariant target classifiers

Canonical collection observations are obtained from the existing certified
normalizer. Equation stability is a separate local obligation: a bag
normalizer alone need not decide any additional authored equation. The
structural-modal adapter uses the framework's proved invariant reading rather
than assuming that raw constructor observations descend.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.EquationProfiles

open Mettapedia.OSLF.MeTTaIL Syntax GeneralOccurrenceFrontier Complete
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

variable {request : Request}

/-- A test of normal forms descends when the supplied normalizer handles the
collection/extrusion laws and is stable under each authored equation. -/
def normalizedTest (nf : Pattern → Pattern)
    (normalizer : Coherence.Normalizer
      (CanonicalBags.StandardStep (Normalized.laws request.plan) (Normalized.extrusions request.plan)) nf)
    (equations : ∀ first second,
      GeneralOccurrenceSemantics.Equation request.plan request.bound request.expected first second →
      nf first = nf second) (observe : Pattern → Bool) : Test request where
  accepts term := observe (nf term)
  invariant first second equivalent := by
    have same : nf first = nf second := by
      induction equivalent with
      | rel a b step =>
        rcases step with equation | law
        · exact equations a b equation
        · exact normalizer.canonical a b law
      | refl => rfl
      | symm _ _ _ ih => exact ih.symm
      | trans _ _ _ _ _ first second => exact first.trans second
    exact congrArg observe same

/-- Certified permutation/flattening/unit normalization, with no implicitly
added wrapper identities or scope-extrusion laws. Authored equations still
have to preserve this normal form. -/
def collectionTest
    (noExtrusions : Normalized.extrusions request.plan = [])
    (equations : ∀ first second,
      GeneralOccurrenceSemantics.Equation request.plan request.bound request.expected first second →
      CanonicalBags.lawNormal (Normalized.laws request.plan) first =
        CanonicalBags.lawNormal (Normalized.laws request.plan) second)
    (observe : Pattern → Bool) : Test request :=
  normalizedTest (CanonicalBags.lawNormal (Normalized.laws request.plan))
    (by rw [noExtrusions]; exact Coherence.lawNormalizer _) equations observe

/-- Any executable boolean observation proved to implement an already
invariant semantic predicate may be used without normalizing its argument. -/
def Test.ofPredicate (predicate : EquationPredicate
      (Presented.gslt request.plan request.bound request.expected))
    (check : Pattern → Bool) (exact : ∀ term, check term = true ↔ predicate term) : Test request where
  accepts := check
  invariant first second equivalent := by
    have iff : check first = true ↔ check second = true :=
      (exact first).trans ((predicate.2 equivalent).trans (exact second).symm)
    cases firstValue : check first <;> cases secondValue : check second <;> simp_all

/-- A formula of the invariant structural-modal semantics determines an
equation predicate. This construction reuses the existing invariance proof;
no decidability or termination is inferred from it. -/
def structuralPredicate (environment : Engine.RelationEnv) (language : LanguageDef)
    (formula : Mettapedia.OSLF.StructuralModal.Formula) :
    EquationPredicate (Mettapedia.OSLF.Framework.TypeSynthesis.langGSLTUsing environment language) :=
  Mettapedia.OSLF.StructuralModal.EquationInvariance.moduloPredicate environment language formula

end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.EquationProfiles
