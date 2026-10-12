import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeMonotoneNaming

/-!
# Native proof certificates earn the complete lattice operator

Checked finite evidence for the ordinary quantified native proposition
proves monotonicity of the actual native operator's complete predicate
readout. The lattice operator is constructed from this proof, rather than
receiving a semantic monotonicity law in a model interface.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeMonotoneCertificate

open _root_.CategoryTheory Mettapedia.TypeTheory Mettapedia.GSLT.Topos
open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open ContextualLocalUniverses ContextualModelTelescopes
open NativeLocalTypeFormers NativeLocalTypeOperations
open PresheafNativePropositionReadout DisplayedPresheafComprehension
open PredicateVariables NativeMonotoneFunctions NativeMonotoneReadout NativeMonotoneNaming

universe u v
variable {C : Type u} [Category.{u} C] {P : Cᵒᵖ ⥤ Type u}
variable {S : Symbols.{v}} {n : Nat} {signature : Signature S}

theorem monotonicityMeaning_body (A : NativeType P) (operator : (operatorType A).decoded.sections)
    (certified : monotonicityMeaning A operator = ⊤) : monotonicityBody A operator = ⊤ := by
  apply (PresheafPredicateAssumptionLogic.universal_top_iff
    (totalProjection (predicate (argumentType A)).decoded) _).mp
  exact (PresheafPredicateAssumptionLogic.universal_top_iff
    (totalProjection (predicate A).decoded) _).mp certified

theorem native_operator_monotone (A : NativeType P) (operator : (operatorType A).decoded.sections)
    (certified : monotonicityMeaning A operator = ⊤) : Monotone (action A operator) := by
  intro first second below
  have specialized := monotonicity_specialization A operator (predicateName A first) (predicateName A second)
  rw [monotonicityMeaning_body A operator certified, preimage_top'] at specialized
  have implication := himp_eq_top_iff.mp specialized.symm
  have antecedent : inclusionMeaning A (predicateName A first) (predicateName A second) = ⊤ := by
    apply (inclusionMeaning_top_iff A _ _).mpr
    simpa only [predicateBody_name] using below
  have consequent : inclusionMeaning A
      (applyValue (predicate A) operator (predicateName A first))
      (applyValue (predicate A) operator (predicateName A second)) = ⊤ := by
    apply top_unique
    rw [← antecedent]
    exact implication
  exact (inclusionMeaning_top_iff A _ _).mp consequent

variable [DecidableEq S.TypeSymbol] [DecidableEq S.TermSymbol] [DecidableEq S.PredicateSymbol]

theorem checked_monotonicity (model : ModelData S C) (realized : SignatureRealization model signature)
    (contextCode : ContextExpr S n) (context : Scope C n)
    (domain : TypeExpr S n) (A : NativeType context.1) (operatorCode : TermExpr S n)
    (operator : (operatorType A).decoded.sections)
    (contextRead : model.evaluateContext contextCode = some context)
    (domainRead : model.evaluateType context domain = some A)
    (operatorRead : model.evaluateTerm context operatorCode = some ⟨operatorType A,operator⟩)
    (certificate : Certificates.Refinement.Certificate signature)
    (accepted : Certificates.Refinement.check certificate
      (.entails contextCode (NativeMonotoneSyntax.monotonicity domain operatorCode)) = true) :
    monotonicityMeaning A operator = ⊤ := by
  have truth := (Certificates.Refinement.checked_native_sound model realized certificate _ accepted).entailsAt
    context contextRead
  exact Option.some.inj ((evaluate_monotonicity model context domain A operatorCode operator
    domainRead operatorRead).symm.trans truth)

/-- The checked evidence, full native operator term and actual evaluator
readout determine the monotone lattice map. -/
noncomputable def checkedOperator (model : ModelData S C) (realized : SignatureRealization model signature)
    (contextCode : ContextExpr S n) (context : Scope C n)
    (domain : TypeExpr S n) (A : NativeType context.1) (operatorCode : TermExpr S n)
    (operator : (operatorType A).decoded.sections)
    (contextRead : model.evaluateContext contextCode = some context)
    (domainRead : model.evaluateType context domain = some A)
    (operatorRead : model.evaluateTerm context operatorCode = some ⟨operatorType A,operator⟩)
    (certificate : Certificates.Refinement.Certificate signature)
    (accepted : Certificates.Refinement.check certificate
      (.entails contextCode (NativeMonotoneSyntax.monotonicity domain operatorCode)) = true) :
    Subfunctor (totalSpace A.decoded) →o Subfunctor (totalSpace A.decoded) where
  toFun := action A operator
  monotone' := native_operator_monotone A operator
    (checked_monotonicity model realized contextCode context domain A operatorCode operator
      contextRead domainRead operatorRead certificate accepted)

end Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeMonotoneCertificate
