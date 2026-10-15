import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.PredicateNaming
import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeMonotoneSyntax

/-!
# Actual native endomorphism values and predicate readout

The semantic operator is the actual native dependent-product section, and
application is the existing native application operation. Casts identify the
constant codomain after supplying its argument. Complete predicate sections
are equivalent to subobjects through the native proposition classifier.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeMonotoneFunctions

open _root_.CategoryTheory Mettapedia.TypeTheory Mettapedia.GSLT.Topos
open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open ContextualLocalUniverses ContextualModelTelescopes ContextualTypeOperations
open NativeLocalTypeFormers NativeLocalTypeOperations
open PresheafNativePropositionReadout PresheafNativePropositionSubstitution
open DisplayedPresheafComprehension PredicateVariables PredicateNaming

universe u v
variable {C : Type u} [Category.{u} C] {P Q R : Cᵒᵖ ⥤ Type u}
variable {S : Symbols.{v}} {n : Nat}

theorem value_substitute_comp (value : NativeValue P) (first : Q ⟶ P) (second : R ⟶ Q) :
    Value.substitute (K := (NativeModel C).toCwf) value (second ≫ first) =
      Value.substitute (K := (NativeModel C).toCwf)
        (Value.substitute (K := (NativeModel C).toCwf) value first) second :=
  Value.substitute_composition value first second

theorem predicateValue_substitution (A : NativeType P)
    (function : (predicate A).decoded.sections) (substitution : Q ⟶ P) :
    Value.substitute (K := (NativeModel C).toCwf) (⟨predicate A,function⟩ : NativeValue P) substitution =
      ⟨predicate (A.reindex substitution),weakenFunction A function substitution⟩ :=
  nativeValue_cast (predicate_reindex A substitution) _

noncomputable def endomorphism (B : NativeType P) : NativeType P :=
  NativeLocalTypeFormers.pi B (B.reindex (totalProjection B.decoded))

theorem applied_type (B : NativeType P) (argument : B.decoded.sections) :
    (B.reindex (totalProjection B.decoded)).reindex (sectionLift B.decoded argument) = B := by
  rw [← LocalType.reindex_comp]
  change B.reindex (sectionLift B.decoded argument ≫ totalProjection B.decoded) = B
  rw [projection_section]
  exact LocalType.reindex_id B

noncomputable def applyValue (B : NativeType P)
    (function : (endomorphism B).decoded.sections) (argument : B.decoded.sections) :
    B.decoded.sections :=
  castTerm (applied_type B argument) (NativeLocalTypeOperations.app function argument)

theorem application_value (B : NativeType P)
    (function : (endomorphism B).decoded.sections) (argument : B.decoded.sections) :
    (⟨(B.reindex (totalProjection B.decoded)).reindex (sectionLift B.decoded argument),
      NativeLocalTypeOperations.app function argument⟩ : NativeValue P) =
      ⟨B,applyValue B function argument⟩ := nativeValue_cast (applied_type B argument) _

theorem constant_body_reindex (B : NativeType P) (substitution : Q ⟶ P) :
    (B.reindex (totalProjection B.decoded)).reindex (totalReindexMap substitution B.decoded) =
      (B.reindex substitution).reindex (totalProjection (B.reindex substitution).decoded) := by
  rw [← LocalType.reindex_comp, ← LocalType.reindex_comp]
  apply congrArg (fun map => B.reindex map)
  change totalReindexMap substitution B.decoded ≫ totalProjection B.decoded =
    totalProjection (B.reindex substitution).decoded ≫ substitution
  ext world value
  rfl

theorem endomorphism_reindex (B : NativeType P) (substitution : Q ⟶ P) :
    (endomorphism B).reindex substitution = endomorphism (B.reindex substitution) := by
  rw [endomorphism, pi_reindex]
  apply congrArg (NativeLocalTypeFormers.pi (B.reindex substitution))
  exact constant_body_reindex B substitution

noncomputable def weakenEndomorphism (B : NativeType P)
    (function : (endomorphism B).decoded.sections) (substitution : Q ⟶ P) :
    (endomorphism (B.reindex substitution)).decoded.sections :=
  castTerm (endomorphism_reindex B substitution)
    (ContextualLocalUniverses.substituteTerm (type := endomorphism B) function substitution)

theorem dependent_application_equal (A : NativeType P)
    {first second : NativeType (totalSpace A.decoded)} (same : first = second)
    (before : (NativeLocalTypeFormers.pi A first).decoded.sections)
    (after : (NativeLocalTypeFormers.pi A second).decoded.sections)
    (functions : HEq before after) (argument : A.decoded.sections) :
    (⟨first.reindex (sectionLift A.decoded argument),NativeLocalTypeOperations.app before argument⟩ :
      NativeValue P) =
      ⟨second.reindex (sectionLift A.decoded argument),NativeLocalTypeOperations.app after argument⟩ := by
  cases same
  cases functions
  rfl

/-- Actual application of an arbitrary native endomorphism commutes with
substitution, including the returned dependent value. -/
theorem applyValue_substitution (B : NativeType P)
    (function : (endomorphism B).decoded.sections) (argument : B.decoded.sections)
    (substitution : Q ⟶ P) :
    ContextualLocalUniverses.substituteTerm (type := B) (applyValue B function argument) substitution =
      applyValue (B.reindex substitution) (weakenEndomorphism B function substitution)
        (ContextualLocalUniverses.substituteTerm (type := B) argument substitution) := by
  let body := B.reindex (totalProjection B.decoded)
  let lifted := totalReindexMap substitution B.decoded
  let argument' := ContextualLocalUniverses.substituteTerm (type := B) argument substitution
  let function' := ContextualTypeOperations.reindexFunction (products C)
    (products_formation_substitution C) substitution function
  have related : HEq (ContextualLocalUniverses.substituteTerm (type := endomorphism B)
      function substitution) function' :=
    (ContextualTypeOperations.reindexFunction_heq (products C)
      (products_formation_substitution C) substitution function).symm
  have square := Mettapedia.TypeTheory.ContextualTypeOperations.selfExtend_substitution
    (C := (NativeModel C).toCwf) substitution argument
  have resultType : (body.reindex (sectionLift B.decoded argument)).reindex substitution =
      (body.reindex lifted).reindex (sectionLift (B.reindex substitution).decoded argument') := by
    rw [← LocalType.reindex_comp, ← LocalType.reindex_comp]
    exact congrArg (fun map => body.reindex map) square.symm
  have naturalRaw : Value.substitute (K := (NativeModel C).toCwf) (⟨body.reindex (sectionLift B.decoded argument),
      NativeLocalTypeOperations.app function argument⟩ : NativeValue P) substitution =
      ⟨(body.reindex lifted).reindex (sectionLift (B.reindex substitution).decoded argument'),
        NativeLocalTypeOperations.app function' argument'⟩ :=
    Sigma.ext resultType (NativeLocalTypeOperations.app_reindex substitution function argument function' related)
  have constantBody := constant_body_reindex B substitution
  have converted := dependent_application_equal (B.reindex substitution) constantBody function'
    (weakenEndomorphism B function substitution)
    (related.symm.trans (cast_heq _ _).symm) argument'
  have normalized : Value.substitute (K := (NativeModel C).toCwf)
      (⟨B,applyValue B function argument⟩ : NativeValue P) substitution =
      ⟨B.reindex substitution,applyValue (B.reindex substitution)
        (weakenEndomorphism B function substitution) argument'⟩ :=
    (congrArg (fun value : NativeValue P => Value.substitute (K := (NativeModel C).toCwf) value substitution)
      (application_value B function argument).symm).trans
        (naturalRaw.trans (converted.trans (application_value (B.reindex substitution) _ _)))
  exact eq_of_heq (Sigma.mk.inj normalized).2

noncomputable def predicateBody (A : NativeType P) (function : (predicate A).decoded.sections) :
    Subfunctor (totalSpace A.decoded) :=
  nativeHolds ((functionEquiv A (nativeOmega (totalSpace A.decoded))).symm function)

noncomputable def predicateName (A : NativeType P) (meaning : Subfunctor (totalSpace A.decoded)) :
    (predicate A).decoded.sections := NativeLocalTypeOperations.lam (nativeQuote meaning)

theorem predicateBody_name (A : NativeType P) (meaning : Subfunctor (totalSpace A.decoded)) :
    predicateBody A (predicateName A meaning) = meaning := by
  unfold predicateBody predicateName NativeLocalTypeOperations.lam
  rw [Equiv.symm_apply_apply, nativeHolds_nativeQuote]

theorem predicateName_body (A : NativeType P) (function : (predicate A).decoded.sections) :
    predicateName A (predicateBody A function) = function := by
  unfold predicateName predicateBody
  rw [nativeQuote_nativeHolds]
  exact NativeLocalTypeOperations.eta function

theorem predicateBody_substitution (A : NativeType P)
    (function : (predicate A).decoded.sections) (substitution : Q ⟶ P) :
    predicateBody (A.reindex substitution) (weakenFunction A function substitution) =
      (predicateBody A function).preimage (totalReindexMap substitution A.decoded) := by
  rw [predicateBody, functionBody_substitution, nativeHolds_substituteNative]
  rfl

theorem predicateName_substitution (A : NativeType P)
    (meaning : Subfunctor (totalSpace A.decoded)) (substitution : Q ⟶ P) :
    weakenFunction A (predicateName A meaning) substitution =
      predicateName (A.reindex substitution) (meaning.preimage (totalReindexMap substitution A.decoded)) := by
  rw [← predicateName_body (A.reindex substitution)
    (weakenFunction A (predicateName A meaning) substitution),
    predicateBody_substitution, predicateBody_name]

noncomputable abbrev operatorType (A : NativeType P) := endomorphism (predicate A)

theorem operator_reindex (A : NativeType P) (substitution : Q ⟶ P) :
    (operatorType A).reindex substitution = operatorType (A.reindex substitution) :=
  (endomorphism_reindex (predicate A) substitution).trans
    (congrArg endomorphism (predicate_reindex A substitution))

noncomputable def weakenOperator (A : NativeType P)
    (operator : (operatorType A).decoded.sections) (substitution : Q ⟶ P) :
    (operatorType (A.reindex substitution)).decoded.sections :=
  castTerm (operator_reindex A substitution)
    (ContextualLocalUniverses.substituteTerm (type := operatorType A) operator substitution)

theorem operatorValue_substitution (A : NativeType P)
    (operator : (operatorType A).decoded.sections) (substitution : Q ⟶ P) :
    Value.substitute (K := (NativeModel C).toCwf) (⟨operatorType A,operator⟩ : NativeValue P) substitution =
      ⟨operatorType (A.reindex substitution),weakenOperator A operator substitution⟩ :=
  nativeValue_cast (operator_reindex A substitution) _

theorem applyValue_values_equal {first second : NativeType P}
    (beforeFunction : (endomorphism first).decoded.sections)
    (afterFunction : (endomorphism second).decoded.sections)
    (beforeArgument : first.decoded.sections) (afterArgument : second.decoded.sections)
    (functions : (⟨endomorphism first,beforeFunction⟩ : NativeValue P) =
      ⟨endomorphism second,afterFunction⟩)
    (arguments : (⟨first,beforeArgument⟩ : NativeValue P) = ⟨second,afterArgument⟩) :
    (⟨first,applyValue first beforeFunction beforeArgument⟩ : NativeValue P) =
      ⟨second,applyValue second afterFunction afterArgument⟩ := by
  have types := congrArg Sigma.fst arguments
  cases types
  have functionSame := eq_of_heq (Sigma.mk.inj functions).2
  have argumentSame := eq_of_heq (Sigma.mk.inj arguments).2
  rw [functionSame,argumentSame]

/-- Both applications and their full returned predicate functions are
transported by the actual native substitution operation. -/
theorem operatorApplication_substitution (A : NativeType P)
    (operator : (operatorType A).decoded.sections) (candidate : (predicate A).decoded.sections)
    (substitution : Q ⟶ P) :
    weakenFunction A (applyValue (predicate A) operator candidate) substitution =
      applyValue (predicate (A.reindex substitution))
        (weakenOperator A operator substitution) (weakenFunction A candidate substitution) := by
  have oldFunction := nativeValue_cast (endomorphism_reindex (predicate A) substitution)
    (ContextualLocalUniverses.substituteTerm (type := operatorType A) operator substitution)
  have newFunction := nativeValue_cast (operator_reindex A substitution)
    (ContextualLocalUniverses.substituteTerm (type := operatorType A) operator substitution)
  have newArgument := nativeValue_cast (predicate_reindex A substitution)
    (ContextualLocalUniverses.substituteTerm (type := predicate A) candidate substitution)
  have output := applyValue_values_equal
    (weakenEndomorphism (predicate A) operator substitution) (weakenOperator A operator substitution)
    (ContextualLocalUniverses.substituteTerm (type := predicate A) candidate substitution)
    (weakenFunction A candidate substitution) (oldFunction.symm.trans newFunction) newArgument
  have returned := applyValue_substitution (predicate A) operator candidate substitution
  have normalized := nativeValue_cast (predicate_reindex A substitution)
    (ContextualLocalUniverses.substituteTerm (type := predicate A)
      (applyValue (predicate A) operator candidate) substitution)
  have values : (⟨predicate (A.reindex substitution),
      weakenFunction A (applyValue (predicate A) operator candidate) substitution⟩ : NativeValue Q) =
      ⟨predicate (A.reindex substitution),applyValue (predicate (A.reindex substitution))
        (weakenOperator A operator substitution) (weakenFunction A candidate substitution)⟩ :=
    normalized.symm.trans ((congrArg (fun term =>
      (⟨(predicate A).reindex substitution,term⟩ : NativeValue Q)) returned).trans output)
  exact eq_of_heq (Sigma.mk.inj values).2

theorem evaluate_operator_weaken (model : ModelData S C) (context : Scope C n)
    (operatorCode : TermExpr S n) (A B : NativeType context.1)
    (operator : (operatorType A).decoded.sections)
    (operatorRead : model.evaluateTerm context operatorCode = some ⟨operatorType A,operator⟩) :
    model.evaluateTerm (context.snoc B) (operatorCode.rename Fin.succ) =
      some ⟨operatorType (A.reindex (totalProjection B.decoded)),
        weakenOperator A operator (totalProjection B.decoded)⟩ := by
  have read := model.evaluateTerm_rename (products_substitution C) operatorCode
    (context.snoc B) context Fin.succ (ModelRenaming.weaken context B)
    ⟨operatorType A,operator⟩ operatorRead
  exact read.trans (congrArg some (nativeValue_cast (operator_reindex A _) _))

noncomputable def action (A : NativeType P) (operator : (operatorType A).decoded.sections)
    (candidate : Subfunctor (totalSpace A.decoded)) : Subfunctor (totalSpace A.decoded) :=
  predicateBody A (applyValue (predicate A) operator (predicateName A candidate))

theorem action_substitution (A : NativeType P) (operator : (operatorType A).decoded.sections)
    (candidate : Subfunctor (totalSpace A.decoded)) (substitution : Q ⟶ P) :
    (action A operator candidate).preimage (totalReindexMap substitution A.decoded) =
      action (A.reindex substitution) (weakenOperator A operator substitution)
        (candidate.preimage (totalReindexMap substitution A.decoded)) := by
  rw [action, ← predicateBody_substitution, operatorApplication_substitution,
    predicateName_substitution]
  rfl

/-- The arbitrary full native operator is evaluated with the ordinary Π former. -/
theorem evaluate_operatorType (model : ModelData S C) (context : Scope C n)
    (domain : TypeExpr S n) (A : NativeType context.1)
    (domainRead : model.evaluateType context domain = some A) :
    model.evaluateType context (NativeMonotoneSyntax.operatorType domain) = some (operatorType A) := by
  have predicateRead := FixedPointSyntax.evaluate_predicateType model context domain A domainRead
  exact model.evaluate_pi context _ _ _ _ predicateRead
    (model.evaluateType_rename (products_substitution C) (FixedPointSyntax.predicateType domain)
      (context.snoc (predicate A)) context Fin.succ
      (ModelRenaming.weaken context (predicate A)) (predicate A) predicateRead)

/-- Application executes the authored operator term and retains its entire
native predicate value; no external transformation is supplied. -/
theorem evaluate_applyOperator (model : ModelData S C) (context : Scope C n)
    (domain : TypeExpr S n) (A : NativeType context.1) (operatorCode candidateCode : TermExpr S n)
    (operator : (operatorType A).decoded.sections) (candidate : (predicate A).decoded.sections)
    (domainRead : model.evaluateType context domain = some A)
    (operatorRead : model.evaluateTerm context operatorCode = some ⟨operatorType A,operator⟩)
    (candidateRead : model.evaluateTerm context candidateCode = some ⟨predicate A,candidate⟩) :
    model.evaluateTerm context (NativeMonotoneSyntax.applyOperator domain operatorCode candidateCode) =
      some ⟨predicate A,applyValue (predicate A) operator candidate⟩ := by
  have predicateRead := FixedPointSyntax.evaluate_predicateType model context domain A domainRead
  have bodyRead := model.evaluateType_rename (products_substitution C) (FixedPointSyntax.predicateType domain)
    (context.snoc (predicate A)) context Fin.succ
    (ModelRenaming.weaken context (predicate A)) (predicate A) predicateRead
  exact (model.evaluate_application context _ _ (predicate A) _ predicateRead bodyRead
    operatorCode candidateCode operator candidate operatorRead candidateRead).trans
      (congrArg some (application_value (predicate A) operator candidate))

end Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeMonotoneFunctions
