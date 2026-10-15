import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.PredicateReification
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementRenamingEvaluation

/-!
# Actual bound predicate variables in generated native formulas

The predicate variable is the actual generic native function variable.
Typed casts use the earned product substitution law. Argument weakening is
the original capture-avoiding syntax renaming and telescope substitution.
The resulting application readout calls the one native evaluator.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.PredicateVariables

open _root_.CategoryTheory Mettapedia.TypeTheory Mettapedia.GSLT.Topos
open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open NativeLocalTypeFormers NativeLocalTypeOperations ContextualLocalUniverses
open PresheafNativePropositionReadout DisplayedPresheafComprehension
open PresheafNativePropositionSubstitution

universe u v
variable {S : Symbols.{v}} {C : Type u} [Category.{u} C] {n : Nat}
variable {P Q : Cᵒᵖ ⥤ Type u}

noncomputable abbrev predicate (A : NativeType P) :=
  NativeLocalTypeFormers.pi A (nativeOmega (totalSpace A.decoded))

theorem predicate_reindex (A : NativeType P) (substitution : Q ⟶ P) :
    (predicate A).reindex substitution = predicate (A.reindex substitution) := by
  rw [predicate, pi_reindex, nativeOmega_reindex]

def castTerm {first second : NativeType P} (same : first = second)
    (value : first.decoded.sections) : second.decoded.sections :=
  cast (congrArg (fun type : NativeType P => ↥type.decoded.sections) same) value

theorem nativeValue_cast {first second : NativeType P} (same : first = second)
    (value : first.decoded.sections) :
    (⟨first, value⟩ : NativeValue P) = ⟨second, castTerm same value⟩ :=
  Sigma.ext same (cast_heq _ _).symm

noncomputable def generic (A : NativeType P) :
    (predicate (A.reindex (totalProjection (predicate A).decoded))).decoded.sections :=
  castTerm (predicate_reindex A (totalProjection (predicate A).decoded))
    ((NativeModel C).toCwf.vz (predicate A))

theorem evaluate_generic (model : ModelData S C) (context : Scope C n) (A : NativeType context.1) :
    model.evaluateTerm (context.snoc (predicate A)) (.var 0) =
      some ⟨predicate (A.reindex (totalProjection (predicate A).decoded)), generic A⟩ := by
  change some (⟨(predicate A).reindex (totalProjection (predicate A).decoded),
    (NativeModel C).toCwf.vz (predicate A)⟩ :
      NativeValue (totalSpace (predicate A).decoded)) = _
  exact congrArg some (nativeValue_cast (predicate_reindex A _) _)

noncomputable def weakenFunction (A : NativeType P)
    (function : (predicate A).decoded.sections) (substitution : Q ⟶ P) :
    (predicate (A.reindex substitution)).decoded.sections :=
  castTerm (predicate_reindex A substitution)
    (ContextualLocalUniverses.substituteTerm (type := predicate A) function substitution)

private theorem uncurry_heq (domain : NativeType P)
    {first second : NativeType (totalSpace domain.decoded)} (same : first = second)
    (before : (NativeLocalTypeFormers.pi domain first).decoded.sections)
    (after : (NativeLocalTypeFormers.pi domain second).decoded.sections)
    (functions : HEq before after) :
    HEq ((functionEquiv domain first).symm before) ((functionEquiv domain second).symm after) := by
  cases same
  cases functions
  rfl

/-- The full uncurried native predicate body, not only its value at one
argument, commutes with actual contextual substitution. -/
theorem functionBody_substitution (A : NativeType P)
    (function : (predicate A).decoded.sections) (substitution : Q ⟶ P) :
    (functionEquiv (A.reindex substitution)
      (nativeOmega (totalSpace (A.reindex substitution).decoded))).symm
        (weakenFunction A function substitution) =
      substituteNative (totalReindexMap substitution A.decoded)
        ((functionEquiv A (nativeOmega (totalSpace A.decoded))).symm function) := by
  let lifted := totalReindexMap substitution A.decoded
  let original := (nativeOmega (totalSpace A.decoded)).reindex lifted
  have omegaSame : original = nativeOmega (totalSpace (A.reindex substitution).decoded) :=
    nativeOmega_reindex lifted
  let oldFunction := castTerm (congrArg (NativeLocalTypeFormers.pi (A.reindex substitution))
    omegaSame.symm) (weakenFunction A function substitution)
  have related : HEq (ContextualLocalUniverses.substituteTerm (type := predicate A)
      function substitution) oldFunction :=
    (cast_heq _ _).symm.trans (cast_heq _ _).symm
  have bodies := functionEquiv_inverse_substitution substitution A
    (nativeOmega (totalSpace A.decoded)) function oldFunction related
  have readback := uncurry_heq (A.reindex substitution) omegaSame.symm
    (weakenFunction A function substitution) oldFunction (cast_heq _ _).symm
  apply eq_of_heq
  exact readback.trans (bodies.trans (cast_heq _ _).symm)

/-- Applying a substituted bound predicate preserves its complete truth
readout and its supplied dependent argument. -/
theorem application_substitution (A : NativeType P)
    (function : (predicate A).decoded.sections) (argument : A.decoded.sections)
    (substitution : Q ⟶ P) :
    nativeHolds (FixedPointSyntax.applicationValue (A.reindex substitution)
      (weakenFunction A function substitution)
      (ContextualLocalUniverses.substituteTerm (type := A) argument substitution)) =
        (nativeHolds (FixedPointSyntax.applicationValue A function argument)).preimage substitution := by
  rw [FixedPointSyntax.applicationValue_holds, functionBody_substitution,
    nativeHolds_substituteNative, ← Subfunctor.preimage_comp,
    FixedPointSyntax.applicationValue_holds, ← Subfunctor.preimage_comp]
  apply congrArg
  exact Mettapedia.TypeTheory.ContextualTypeOperations.selfExtend_substitution
    (C := (NativeModel C).toCwf) substitution argument

theorem evaluate_function_weaken (model : ModelData S C) (context : Scope C n)
    (functionCode : TermExpr S n) (A B : NativeType context.1)
    (function : (predicate A).decoded.sections)
    (functionRead : model.evaluateTerm context functionCode = some ⟨predicate A, function⟩) :
    model.evaluateTerm (context.snoc B) (functionCode.rename Fin.succ) =
      some ⟨predicate (A.reindex (totalProjection B.decoded)),
        weakenFunction A function (totalProjection B.decoded)⟩ := by
  have renamed := model.evaluateTerm_rename (products_substitution C) functionCode
    (context.snoc B) context Fin.succ (ModelRenaming.weaken context B)
    ⟨predicate A, function⟩ functionRead
  exact renamed.trans (congrArg some (nativeValue_cast (predicate_reindex A _) _))

noncomputable abbrev argumentType (A : NativeType P) :=
  A.reindex (totalProjection (predicate A).decoded)

noncomputable def boundMembership (A : NativeType P) :
    Subfunctor (totalSpace (argumentType A).decoded) :=
  nativeHolds (FixedPointSyntax.applicationValue
    ((argumentType A).reindex (totalProjection (argumentType A).decoded))
    (weakenFunction (argumentType A) (generic A)
      (totalProjection (argumentType A).decoded))
    ((NativeModel C).toCwf.vz (argumentType A)))

/-- Both native binders are actual context extensions. In particular the
predicate occurrence is the weakened earlier variable, not an atomic oracle. -/
theorem evaluate_candidateAt (model : ModelData S C) (context : Scope C n)
    (domain : TypeExpr S n) (A : NativeType context.1)
    (domainRead : model.evaluateType context domain = some A) :
    model.evaluatePredicate ((context.snoc (predicate A)).snoc (argumentType A))
      (FixedPointSyntax.candidateAt domain) = some (boundMembership A) := by
  have firstDomain := model.evaluateType_rename (products_substitution C) domain
    (context.snoc (predicate A)) context Fin.succ
    (ModelRenaming.weaken context (predicate A)) A domainRead
  have doubleDomain := model.evaluateType_rename (products_substitution C)
    (domain.rename Fin.succ) ((context.snoc (predicate A)).snoc (argumentType A))
    (context.snoc (predicate A)) Fin.succ
    (ModelRenaming.weaken (context.snoc (predicate A)) (argumentType A))
    (argumentType A) firstDomain
  have functionRead := evaluate_function_weaken model (context.snoc (predicate A)) (.var 0)
    (argumentType A) (argumentType A) (generic A) (evaluate_generic model context A)
  have argumentRead :
      model.evaluateTerm ((context.snoc (predicate A)).snoc (argumentType A)) (.var 0) =
        some ⟨(argumentType A).reindex (totalProjection (argumentType A).decoded),
          (NativeModel C).toCwf.vz (argumentType A)⟩ := rfl
  exact FixedPointSyntax.evaluate_application model _ _ _ (.var 1) (.var 0) _ _
    doubleDomain functionRead argumentRead

/-- The tested argument is weakened through the actual predicate binder.
The bound predicate has no independently supplied truth interpretation. -/
theorem evaluate_application_under_predicate (model : ModelData S C) (context : Scope C n)
    (domain : TypeExpr S n) (tested : TermExpr S n) (A : NativeType context.1)
    (value : A.decoded.sections)
    (domainRead : model.evaluateType context domain = some A)
    (valueRead : model.evaluateTerm context tested = some ⟨A, value⟩) :
    model.evaluatePredicate (context.snoc (predicate A))
      (FixedPointSyntax.application (domain.rename Fin.succ) (.var 0)
        (tested.rename Fin.succ)) =
      some (nativeHolds (FixedPointSyntax.applicationValue
        (A.reindex (totalProjection (predicate A).decoded)) (generic A)
        (ContextualLocalUniverses.substituteTerm (type := A) value
          (totalProjection (predicate A).decoded)))) := by
  let weaker := ModelRenaming.weaken context (predicate A)
  have domainWeak := model.evaluateType_rename (products_substitution C) domain
    (context.snoc (predicate A)) context Fin.succ weaker A domainRead
  have argumentWeak := model.evaluateTerm_rename (products_substitution C) tested
    (context.snoc (predicate A)) context Fin.succ weaker ⟨A, value⟩ valueRead
  exact FixedPointSyntax.evaluate_application model (context.snoc (predicate A))
    (domain.rename Fin.succ) (A.reindex (totalProjection (predicate A).decoded))
    (.var 0) (tested.rename Fin.succ) (generic A) _ domainWeak
    (evaluate_generic model context A) argumentWeak

end Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.PredicateVariables
