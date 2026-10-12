import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeMonotoneFunctions
import Mettapedia.GSLT.Topos.PresheafPredicateAssumptionLogic

/-!
# Whole native evaluator readout of operator monotonicity

The checked proposition quantifies over the two actual native function
binders. Its antecedent is complete predicate inclusion, and its consequent
is inclusion of the two actual applications of the authored operator.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeMonotoneReadout

open _root_.CategoryTheory Mettapedia.TypeTheory Mettapedia.GSLT.Topos
open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open ContextualLocalUniverses ContextualModelTelescopes
open NativeLocalTypeFormers NativeLocalTypeOperations
open PresheafNativePropositionReadout DisplayedPresheafComprehension
open PredicateVariables PredicateNaming NativeMonotoneFunctions

universe u v
variable {C : Type u} [Category.{u} C] {P Q : Cᵒᵖ ⥤ Type u}
variable {S : Symbols.{v}} {n : Nat}

attribute [local irreducible] NativeLocalTypeFormers.pi PresheafNativePropositionReadout.nativeOmega

noncomputable def inclusionMeaning (A : NativeType P)
    (first second : (predicate A).decoded.sections) : Subfunctor P :=
  forallAlong (totalProjection A.decoded) (predicateBody A first ⇨ predicateBody A second)

theorem inclusionMeaning_top_iff (A : NativeType P)
    (first second : (predicate A).decoded.sections) :
    inclusionMeaning A first second = ⊤ ↔ predicateBody A first ≤ predicateBody A second := by
  rw [inclusionMeaning, PresheafPredicateAssumptionLogic.universal_top_iff, himp_eq_top_iff]

theorem inclusionMeaning_substitution (A : NativeType P)
    (first second : (predicate A).decoded.sections) (substitution : Q ⟶ P) :
    (inclusionMeaning A first second).preimage substitution =
      inclusionMeaning (A.reindex substitution)
        (weakenFunction A first substitution) (weakenFunction A second substitution) := by
  rw [inclusionMeaning, forallAlong_beckChevalley _ _ _ _
    (totalReindexMap_isPullback substitution A.decoded).flip,
    preimage_himp, inclusionMeaning, predicateBody_substitution, predicateBody_substitution]
  rfl

/-- Full inclusion is quantified over the genuine dependent carrier and
evaluates both original function terms at the generic carrier argument. -/
theorem evaluate_inclusion (model : ModelData S C) (context : Scope C n)
    (domain : TypeExpr S n) (A : NativeType context.1) (firstCode secondCode : TermExpr S n)
    (first second : (predicate A).decoded.sections)
    (domainRead : model.evaluateType context domain = some A)
    (firstRead : model.evaluateTerm context firstCode = some ⟨predicate A,first⟩)
    (secondRead : model.evaluateTerm context secondCode = some ⟨predicate A,second⟩) :
    model.evaluatePredicate context (NativeMonotoneSyntax.inclusion domain firstCode secondCode) =
      some (inclusionMeaning A first second) := by
  have domainWeak := model.evaluateType_rename (products_substitution C) domain
    (context.snoc A) context Fin.succ (ModelRenaming.weaken context A) A domainRead
  have genericRead : model.evaluateTerm (context.snoc A) (.var 0) =
      some ⟨A.reindex (totalProjection A.decoded),(NativeModel C).toCwf.vz A⟩ := rfl
  have firstApplied := FixedPointSyntax.evaluate_application model (context.snoc A) _ _
    (firstCode.rename Fin.succ) (.var 0) _ _ domainWeak
    (evaluate_function_weaken model context firstCode A A first firstRead) genericRead
  have secondApplied := FixedPointSyntax.evaluate_application model (context.snoc A) _ _
    (secondCode.rename Fin.succ) (.var 0) _ _ domainWeak
    (evaluate_function_weaken model context secondCode A A second secondRead) genericRead
  have firstBody := firstApplied.trans (congrArg some (generic_application_body A first))
  have secondBody := secondApplied.trans (congrArg some (generic_application_body A second))
  have implication := model.evaluate_implies _ _ _ _ _ firstBody secondBody
  rw [himpPointwise_eq_himp] at implication
  exact model.evaluate_all _ _ _ _ _ domainRead implication

noncomputable abbrev secondArgument (A : NativeType P) := argumentType (argumentType A)

noncomputable abbrev firstCandidate (A : NativeType P) :=
  weakenFunction (argumentType A) (generic A) (totalProjection (predicate (argumentType A)).decoded)

noncomputable abbrev secondCandidate (A : NativeType P) := generic (argumentType A)

noncomputable abbrev twiceOperator (A : NativeType P) (operator : (operatorType A).decoded.sections) :=
  weakenOperator (argumentType A)
    (weakenOperator A operator (totalProjection (predicate A).decoded))
    (totalProjection (predicate (argumentType A)).decoded)

noncomputable def monotonicityBody (A : NativeType P) (operator : (operatorType A).decoded.sections) :
    Subfunctor (totalSpace (predicate (argumentType A)).decoded) :=
  inclusionMeaning (secondArgument A) (firstCandidate A) (secondCandidate A) ⇨
    inclusionMeaning (secondArgument A)
      (applyValue (predicate (secondArgument A)) (twiceOperator A operator) (firstCandidate A))
      (applyValue (predicate (secondArgument A)) (twiceOperator A operator) (secondCandidate A))

noncomputable def monotonicityMeaning (A : NativeType P)
    (operator : (operatorType A).decoded.sections) : Subfunctor P :=
  forallAlong (totalProjection (predicate A).decoded)
    (forallAlong (totalProjection (predicate (argumentType A)).decoded) (monotonicityBody A operator))

theorem evaluate_monotonicity_pair (model : ModelData S C) (context : Scope C n)
    (domain : TypeExpr S n) (A : NativeType context.1)
    (operatorCode firstCode secondCode : TermExpr S n)
    (operator : (operatorType A).decoded.sections) (first second : (predicate A).decoded.sections)
    (domainRead : model.evaluateType context domain = some A)
    (operatorRead : model.evaluateTerm context operatorCode = some ⟨operatorType A,operator⟩)
    (firstRead : model.evaluateTerm context firstCode = some ⟨predicate A,first⟩)
    (secondRead : model.evaluateTerm context secondCode = some ⟨predicate A,second⟩) :
    model.evaluatePredicate context
      (.implies (NativeMonotoneSyntax.inclusion domain firstCode secondCode)
        (NativeMonotoneSyntax.inclusion domain
          (NativeMonotoneSyntax.applyOperator domain operatorCode firstCode)
          (NativeMonotoneSyntax.applyOperator domain operatorCode secondCode))) =
      some (inclusionMeaning A first second ⇨ inclusionMeaning A
        (applyValue (predicate A) operator first) (applyValue (predicate A) operator second)) := by
  have antecedent := evaluate_inclusion model context domain A firstCode secondCode first second
    domainRead firstRead secondRead
  have firstImage := evaluate_applyOperator model context domain A operatorCode firstCode operator first
    domainRead operatorRead firstRead
  have secondImage := evaluate_applyOperator model context domain A operatorCode secondCode operator second
    domainRead operatorRead secondRead
  have consequent := evaluate_inclusion model context domain A _ _ _ _ domainRead firstImage secondImage
  have implication := model.evaluate_implies _ _ _ _ _ antecedent consequent
  rw [himpPointwise_eq_himp] at implication
  exact implication

theorem evaluate_predicate (model : ModelData S C) (context : Scope C n)
    (domain : TypeExpr S n) (A : NativeType context.1)
    (domainRead : model.evaluateType context domain = some A) :
    model.evaluateType context (FixedPointSyntax.predicateType domain) = some (predicate A) :=
  FixedPointSyntax.evaluate_predicateType model context domain A domainRead

theorem evaluate_universal (model : ModelData S C) (context : Scope C n)
    (domain : TypeExpr S n) (body : PropExpr S (n + 1)) (A : NativeType context.1)
    (meaning : Subfunctor (totalSpace A.decoded))
    (domainRead : model.evaluateType context domain = some A)
    (bodyRead : model.evaluatePredicate (context.snoc A) body = some meaning) :
    model.evaluatePredicate context (.all domain body) =
      some (forallAlong (totalProjection A.decoded) meaning) :=
  model.evaluate_all context domain body A meaning domainRead bodyRead

noncomputable def pairScope (context : Scope C n) (A : NativeType context.1) : Scope C (n + 2) :=
  ⟨totalSpace (predicate (argumentType A)).decoded,
    .snoc (.snoc context.2 (predicate A)) (predicate (argumentType A))⟩

theorem evaluate_pair_domain (model : ModelData S C) (context : Scope C n)
    (domain : TypeExpr S n) (A : NativeType context.1)
    (domainRead : model.evaluateType context domain = some A) :
    model.evaluateType (pairScope context A) (domain.rename Fin.succ |>.rename Fin.succ) =
      some (secondArgument A) := by
  have firstDomain := model.evaluateType_rename (products_substitution C) domain
    (context.snoc (predicate A)) context Fin.succ (ModelRenaming.weaken context (predicate A)) A domainRead
  exact model.evaluateType_rename (products_substitution C) (domain.rename Fin.succ)
    (pairScope context A) (context.snoc (predicate A)) Fin.succ
    (ModelRenaming.weaken (context.snoc (predicate A)) (predicate (argumentType A)))
    (argumentType A) firstDomain

theorem evaluate_firstCandidate (model : ModelData S C) (context : Scope C n)
    (A : NativeType context.1) :
    model.evaluateTerm (pairScope context A) (.var 1) =
      some ⟨predicate (secondArgument A),firstCandidate A⟩ :=
  evaluate_function_weaken model (context.snoc (predicate A)) (.var 0)
    (argumentType A) (predicate (argumentType A)) (generic A) (evaluate_generic model context A)

theorem evaluate_secondCandidate (model : ModelData S C) (context : Scope C n)
    (A : NativeType context.1) :
    model.evaluateTerm (pairScope context A) (.var 0) =
      some ⟨predicate (secondArgument A),secondCandidate A⟩ :=
  evaluate_generic model (context.snoc (predicate A)) (argumentType A)

theorem evaluate_twiceOperator (model : ModelData S C) (context : Scope C n)
    (A : NativeType context.1) (operatorCode : TermExpr S n)
    (operator : (operatorType A).decoded.sections)
    (operatorRead : model.evaluateTerm context operatorCode = some ⟨operatorType A,operator⟩) :
    model.evaluateTerm (pairScope context A) (operatorCode.rename Fin.succ |>.rename Fin.succ) =
      some ⟨operatorType (secondArgument A),twiceOperator A operator⟩ := by
  have firstOperator := evaluate_operator_weaken model context operatorCode A (predicate A) operator operatorRead
  exact evaluate_operator_weaken model (context.snoc (predicate A)) (operatorCode.rename Fin.succ)
    (argumentType A) (predicate (argumentType A)) _ firstOperator

set_option backward.isDefEq.respectTransparency true in
theorem evaluate_monotonicity_body (model : ModelData S C) (context : Scope C n)
    (domain : TypeExpr S n) (A : NativeType context.1) (operatorCode : TermExpr S n)
    (operator : (operatorType A).decoded.sections)
    (domainRead : model.evaluateType context domain = some A)
    (operatorRead : model.evaluateTerm context operatorCode = some ⟨operatorType A,operator⟩) :
    model.evaluatePredicate (pairScope context A)
      (NativeMonotoneSyntax.monotonicityAt (domain.rename Fin.succ |>.rename Fin.succ)
        (operatorCode.rename Fin.succ |>.rename Fin.succ) (.var 1) (.var 0)) =
      some (monotonicityBody A operator) := by
  apply @evaluate_monotonicity_pair C inferInstance S (n + 2) model (pairScope context A)
    (domain.rename Fin.succ |>.rename Fin.succ) (secondArgument A)
    (operatorCode.rename Fin.succ |>.rename Fin.succ) (.var 1) (.var 0)
    (twiceOperator A operator) (firstCandidate A) (secondCandidate A)
  · exact evaluate_pair_domain model context domain A domainRead
  · exact evaluate_twiceOperator model context A operatorCode operator operatorRead
  · exact evaluate_firstCandidate model context A
  · exact evaluate_secondCandidate model context A

theorem evaluate_first_predicateType (model : ModelData S C) (context : Scope C n)
    (domain : TypeExpr S n) (A : NativeType context.1)
    (domainRead : model.evaluateType context domain = some A) :
    model.evaluateType (context.snoc (predicate A)) (FixedPointSyntax.predicateType (domain.rename Fin.succ)) =
      some (predicate (argumentType A)) := by
  have firstDomain := model.evaluateType_rename (products_substitution C) domain
    (context.snoc (predicate A)) context Fin.succ (ModelRenaming.weaken context (predicate A)) A domainRead
  exact evaluate_predicate model (context.snoc (predicate A)) _ (argumentType A) firstDomain

theorem evaluate_monotonicity_under_predicate (model : ModelData S C) (context : Scope C n)
    (domain : TypeExpr S n) (A : NativeType context.1) (operatorCode : TermExpr S n)
    (operator : (operatorType A).decoded.sections)
    (domainRead : model.evaluateType context domain = some A)
    (operatorRead : model.evaluateTerm context operatorCode = some ⟨operatorType A,operator⟩) :
    model.evaluatePredicate (context.snoc (predicate A))
      (NativeMonotoneSyntax.monotonicityUnderPredicate domain operatorCode) =
      some (forallAlong (totalProjection (predicate (argumentType A)).decoded) (monotonicityBody A operator)) :=
  evaluate_universal model (context.snoc (predicate A))
    (FixedPointSyntax.predicateType (domain.rename Fin.succ))
    (NativeMonotoneSyntax.monotonicityAt (domain.rename Fin.succ |>.rename Fin.succ)
      (operatorCode.rename Fin.succ |>.rename Fin.succ) (.var 1) (.var 0))
    (predicate (argumentType A)) (monotonicityBody A operator)
    (evaluate_first_predicateType model context domain A domainRead)
    (evaluate_monotonicity_body model context domain A operatorCode operator domainRead operatorRead)

/-- No semantic monotonicity premise is supplied: this computes the full
ordinary native proposition whose finite certificate will be checked. -/
theorem evaluate_monotonicity (model : ModelData S C) (context : Scope C n)
    (domain : TypeExpr S n) (A : NativeType context.1) (operatorCode : TermExpr S n)
    (operator : (operatorType A).decoded.sections)
    (domainRead : model.evaluateType context domain = some A)
    (operatorRead : model.evaluateTerm context operatorCode = some ⟨operatorType A,operator⟩) :
    model.evaluatePredicate context (NativeMonotoneSyntax.monotonicity domain operatorCode) =
      some (monotonicityMeaning A operator) :=
  evaluate_universal model context _ _ (predicate A) _
    (evaluate_predicate model context domain A domainRead)
    (evaluate_monotonicity_under_predicate model context domain A operatorCode operator domainRead operatorRead)

end Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeMonotoneReadout
