import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeMonotonePredicates
import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeMonotoneTransport

/-!
# Complete evaluator meaning of generated native fixed-point predicates

The generated lambdas quote the membership formulas at the actual generic
dependent argument. The generic comprehension diagonal and earned fixed-point
transport identify their complete bodies with the independent lattice
fixed points. This retains native predicate values and every dependent witness.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeMonotonePredicateReadout

open _root_.CategoryTheory Mettapedia.TypeTheory Mettapedia.GSLT.Topos
open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open ContextualLocalUniverses ContextualModelTelescopes NativeLocalTypeFormers NativeLocalTypeOperations
open PresheafNativePropositionReadout DisplayedPresheafComprehension
open PredicateVariables NativeMonotoneFunctions NativeMonotoneReadout NativeMonotoneCertificate
open NativeMonotoneBaseChange NativeMonotoneEvaluation NativeMonotoneComparison NativeMonotoneStability
open NativeMonotonePredicates
open NativeFixedPointEncodings

universe u v
variable {C : Type u} [Category.{u} C] {P Q : Cᵒᵖ ⥤ Type u} {S : Symbols.{v}} {n : Nat}
attribute [local irreducible] NativeLocalTypeFormers.pi PresheafNativePropositionReadout.nativeOmega

theorem least_at_generic (A : NativeType P) (operator : (operatorType A).decoded.sections)
    (certified : monotonicityMeaning A operator = ⊤) :
    least (A.reindex (totalProjection A.decoded)) (weakenOperator A operator (totalProjection A.decoded))
      ((NativeModel C).toCwf.vz A) = leastMeaning (semanticOperator A operator certified) := by
  rw [least_eq_meaning _ _ (checked_monotonicity_reindex A operator certified (totalProjection A.decoded)),
    ← leastEncoding_eq_meaning, ← leastEncoding_eq_meaning]
  change (leastEncoding (operatorAt A operator certified (totalProjection A.decoded))).preimage _ = _
  rw [← NativeMonotoneBaseChange.least_substitution, ← Subfunctor.preimage_comp]
  have diagonal : sectionLift (A.reindex (totalProjection A.decoded)).decoded ((NativeModel C).toCwf.vz A) ≫
      totalReindexMap (totalProjection A.decoded) A.decoded = 𝟙 (totalSpace A.decoded) :=
    ContextualPiEta.lifted_generic_identity (C := (NativeModel C).toCwf) A
  rw [diagonal]
  ext world value
  rfl

theorem greatest_at_generic (A : NativeType P) (operator : (operatorType A).decoded.sections)
    (certified : monotonicityMeaning A operator = ⊤) :
    greatest (A.reindex (totalProjection A.decoded)) (weakenOperator A operator (totalProjection A.decoded))
      ((NativeModel C).toCwf.vz A) = greatestMeaning (semanticOperator A operator certified) := by
  rw [greatest_eq_meaning _ _ (checked_monotonicity_reindex A operator certified (totalProjection A.decoded)),
    ← greatestEncoding_eq_meaning, ← greatestEncoding_eq_meaning]
  change (greatestEncoding (operatorAt A operator certified (totalProjection A.decoded))).preimage _ = _
  rw [← NativeMonotoneBaseChange.greatest_substitution, ← Subfunctor.preimage_comp]
  have diagonal : sectionLift (A.reindex (totalProjection A.decoded)).decoded ((NativeModel C).toCwf.vz A) ≫
      totalReindexMap (totalProjection A.decoded) A.decoded = 𝟙 (totalSpace A.decoded) :=
    ContextualPiEta.lifted_generic_identity (C := (NativeModel C).toCwf) A
  rw [diagonal]
  ext world value
  rfl

theorem evaluate_leastPredicate (model : ModelData S C) (context : Scope C n)
    (domain : TypeExpr S n) (A : NativeType context.1) (operatorCode : TermExpr S n)
    (operator : (operatorType A).decoded.sections) (certified : monotonicityMeaning A operator = ⊤)
    (domainRead : model.evaluateType context domain = some A)
    (operatorRead : model.evaluateTerm context operatorCode = some ⟨operatorType A,operator⟩) :
    model.evaluateTerm context (leastPredicate domain operatorCode) =
      some ⟨predicate A,predicateName A (leastMeaning (semanticOperator A operator certified))⟩ := by
  have domainWeak := model.evaluateType_rename (products_substitution C) domain (context.snoc A) context Fin.succ
    (ModelRenaming.weaken context A) A domainRead
  have genericRead : model.evaluateTerm (context.snoc A) (.var 0) =
      some ⟨A.reindex (totalProjection A.decoded),(NativeModel C).toCwf.vz A⟩ := rfl
  have membership := (evaluate_least model (context.snoc A) (domain.rename Fin.succ) _
    (operatorCode.rename Fin.succ) (.var 0) _ _ domainWeak
    (evaluate_operator_weaken model context operatorCode A A operator operatorRead) genericRead).trans
      (congrArg some (least_at_generic A operator certified))
  exact model.evaluate_lambda context domain .propositions A (nativeOmega (totalSpace A.decoded)) domainRead
    (by rfl) _ _ (model.evaluate_quote _ _ _ membership)

theorem evaluate_greatestPredicate (model : ModelData S C) (context : Scope C n)
    (domain : TypeExpr S n) (A : NativeType context.1) (operatorCode : TermExpr S n)
    (operator : (operatorType A).decoded.sections) (certified : monotonicityMeaning A operator = ⊤)
    (domainRead : model.evaluateType context domain = some A)
    (operatorRead : model.evaluateTerm context operatorCode = some ⟨operatorType A,operator⟩) :
    model.evaluateTerm context (greatestPredicate domain operatorCode) =
      some ⟨predicate A,predicateName A (greatestMeaning (semanticOperator A operator certified))⟩ := by
  have domainWeak := model.evaluateType_rename (products_substitution C) domain (context.snoc A) context Fin.succ
    (ModelRenaming.weaken context A) A domainRead
  have genericRead : model.evaluateTerm (context.snoc A) (.var 0) =
      some ⟨A.reindex (totalProjection A.decoded),(NativeModel C).toCwf.vz A⟩ := rfl
  have membership := (evaluate_greatest model (context.snoc A) (domain.rename Fin.succ) _
    (operatorCode.rename Fin.succ) (.var 0) _ _ domainWeak
    (evaluate_operator_weaken model context operatorCode A A operator operatorRead) genericRead).trans
      (congrArg some (greatest_at_generic A operator certified))
  exact model.evaluate_lambda context domain .propositions A (nativeOmega (totalSpace A.decoded)) domainRead
    (by rfl) _ _ (model.evaluate_quote _ _ _ membership)

theorem leastPredicate_substitution (A : NativeType P) (operator : (operatorType A).decoded.sections)
    (certified : monotonicityMeaning A operator = ⊤) (substitution : Q ⟶ P) :
    weakenFunction A (predicateName A (leastMeaning (semanticOperator A operator certified))) substitution =
      predicateName (A.reindex substitution)
        (leastMeaning (semanticOperator (A.reindex substitution) (weakenOperator A operator substitution)
          (checked_monotonicity_reindex A operator certified substitution))) := by
  rw [predicateName_substitution]
  apply congrArg (predicateName (A.reindex substitution))
  rw [← leastEncoding_eq_meaning, ← leastEncoding_eq_meaning]
  exact NativeMonotoneBaseChange.least_substitution A operator certified substitution

theorem greatestPredicate_substitution (A : NativeType P) (operator : (operatorType A).decoded.sections)
    (certified : monotonicityMeaning A operator = ⊤) (substitution : Q ⟶ P) :
    weakenFunction A (predicateName A (greatestMeaning (semanticOperator A operator certified))) substitution =
      predicateName (A.reindex substitution)
        (greatestMeaning (semanticOperator (A.reindex substitution) (weakenOperator A operator substitution)
          (checked_monotonicity_reindex A operator certified substitution))) := by
  rw [predicateName_substitution]
  apply congrArg (predicateName (A.reindex substitution))
  rw [← greatestEncoding_eq_meaning, ← greatestEncoding_eq_meaning]
  exact NativeMonotoneBaseChange.greatest_substitution A operator certified substitution

theorem leastPredicate_unfold (A : NativeType P) (operator : (operatorType A).decoded.sections)
    (certified : monotonicityMeaning A operator = ⊤) :
    predicateBody A (applyValue (predicate A) operator
      (predicateName A (leastMeaning (semanticOperator A operator certified)))) =
        leastMeaning (semanticOperator A operator certified) :=
  (semanticOperator A operator certified).map_lfp

theorem greatestPredicate_unfold (A : NativeType P) (operator : (operatorType A).decoded.sections)
    (certified : monotonicityMeaning A operator = ⊤) :
    predicateBody A (applyValue (predicate A) operator
      (predicateName A (greatestMeaning (semanticOperator A operator certified)))) =
        greatestMeaning (semanticOperator A operator certified) :=
  (semanticOperator A operator certified).map_gfp

theorem leastPredicate_induction (A : NativeType P) (operator : (operatorType A).decoded.sections)
    (certified : monotonicityMeaning A operator = ⊤) (candidate : (predicate A).decoded.sections)
    (closed : predicateBody A (applyValue (predicate A) operator candidate) ≤ predicateBody A candidate) :
    leastMeaning (semanticOperator A operator certified) ≤ predicateBody A candidate := by
  apply (semanticOperator A operator certified).lfp_le
  change action A operator (predicateBody A candidate) ≤ predicateBody A candidate
  rw [NativeMonotoneStability.action_body]
  exact closed

theorem greatestPredicate_coinduction (A : NativeType P) (operator : (operatorType A).decoded.sections)
    (certified : monotonicityMeaning A operator = ⊤) (candidate : (predicate A).decoded.sections)
    (closed : predicateBody A candidate ≤ predicateBody A (applyValue (predicate A) operator candidate)) :
    predicateBody A candidate ≤ greatestMeaning (semanticOperator A operator certified) := by
  apply (semanticOperator A operator certified).le_gfp
  change predicateBody A candidate ≤ action A operator (predicateBody A candidate)
  rw [NativeMonotoneStability.action_body]
  exact closed

variable {signature : Signature S}
variable [DecidableEq S.TypeSymbol] [DecidableEq S.TermSymbol] [DecidableEq S.PredicateSymbol]

theorem certifiedGenerate_sound (model : ModelData S C) (realized : SignatureRealization model signature)
    (contextCode : ContextExpr S n) (domain : TypeExpr S n) (operatorCode : TermExpr S n)
    (contextCertificate domainCertificate operatorCertificate monotonicityCertificate : Certificates.Refinement.Certificate signature)
    (generated : GeneratedPredicates signature n)
    (result : NativeMonotonePredicates.certifiedGenerate contextCode domain operatorCode
      contextCertificate domainCertificate operatorCertificate monotonicityCertificate = some generated) :
    ∃ (context : Scope C n) (A : NativeType context.1) (operator : (operatorType A).decoded.sections)
      (certified : monotonicityMeaning A operator = ⊤),
      model.evaluateContext contextCode = some context ∧ model.evaluateType context domain = some A ∧
      model.evaluateTerm context operatorCode = some ⟨operatorType A,operator⟩ ∧
      model.evaluateTerm context generated.leastCode =
        some ⟨predicate A,predicateName A (leastMeaning (semanticOperator A operator certified))⟩ ∧
      model.evaluateTerm context generated.greatestCode =
        some ⟨predicate A,predicateName A (greatestMeaning (semanticOperator A operator certified))⟩ := by
  have accepted := (NativeMonotonePredicates.certifiedGenerate_isSome contextCode domain operatorCode
    contextCertificate domainCertificate operatorCertificate monotonicityCertificate).mp
      (show (NativeMonotonePredicates.certifiedGenerate contextCode domain operatorCode
        contextCertificate domainCertificate operatorCertificate monotonicityCertificate).isSome = true by rw [result]; rfl)
  have checked := (checkInputs_exact contextCode domain operatorCode _ _ _ _).mp accepted
  rcases Certificates.Refinement.checked_native_sound model realized contextCertificate _ checked.1 with
    ⟨context,contextRead⟩
  rcases (Certificates.Refinement.checked_native_sound model realized domainCertificate _ checked.2.1).typeAt
    context contextRead with ⟨A,domainRead⟩
  rcases (Certificates.Refinement.checked_native_sound model realized operatorCertificate _ checked.2.2.1).termAt
    context (operatorType A) contextRead (evaluate_operatorType model context domain A domainRead) with ⟨operator,operatorRead⟩
  have certified := checked_monotonicity model realized contextCode context domain A operatorCode operator
    contextRead domainRead operatorRead monotonicityCertificate checked.2.2.2
  have codes := NativeMonotonePredicates.certifiedGenerate_checked contextCode domain operatorCode
    contextCertificate domainCertificate operatorCertificate monotonicityCertificate generated result
  refine ⟨context,A,operator,certified,contextRead,domainRead,operatorRead,?_,?_⟩
  · rw [codes.1]
    exact evaluate_leastPredicate model context domain A operatorCode operator certified domainRead operatorRead
  · rw [codes.2.1]
    exact evaluate_greatestPredicate model context domain A operatorCode operator certified domainRead operatorRead

end Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeMonotonePredicateReadout
