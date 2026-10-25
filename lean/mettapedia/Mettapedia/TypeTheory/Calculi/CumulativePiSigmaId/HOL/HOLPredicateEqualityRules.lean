import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLPredicateEqualitySignature

/-!
# Typed predicate transport in a declared HOL proof family

Predicate equality introduces a function taking a predicate and its proof at
the first endpoint, then returning a proof at the second endpoint. Introduction,
specialization and reuse below construct the actual native lambdas and
applications. They use only the existing implication and universal decoders.
The source declaration signature and the fresh proof-family name are parameters.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false
namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLPredicateEqualityRules

open Presentation Presentation.FormationSensitive FormationSensitiveHOLInterface
open FormationSensitiveHOLGenericProofFamily (proof rawImp universalProposition)
open HOLPredicateEqualitySignature (raw)
open Mettapedia.Logic
universe u v
variable {Base : Type u} {Const : HOL.Ty Base → Type v}
variable (source : LogicalSignature Base Const) (proofName : DeclName)

abbrev rules : Rules Tower.Head :=
  FormationSensitiveHOLGenericProofFamily.rules
    (HOLPredicateEqualitySignature.signature source) proofName

def predicateContext {n : Nat} (context : Tower.Ctx n) (type : HOL.Ty Base) : Tower.Ctx (n + 1) :=
  .snoc context (typeAt source.types n (.arr type .prop))

def atPredicate {n : Nat} (value : Tower.Tm n) : Tower.Tm (n + 1) :=
  .app (.var 0) (rename wk value)

theorem application_typed {n : Nat} {context : Tower.Ctx n} {a b : HOL.Ty Base}
    {function argument : Tower.Tm n}
    (functionTyped : Typing (rules source proofName) context function
      (typeAt source.types n (.arr a b)))
    (argumentTyped : Typing (rules source proofName) context argument (typeAt source.types n a)) :
    Typing (rules source proofName) context (.app function argument) (typeAt source.types n b) := by
  simpa only [inst0, typeAt_subst] using Typing.appElim functionTyped argumentTyped

theorem atPredicate_typed {n : Nat} {context : Tower.Ctx n} {type : HOL.Ty Base}
    {value : Tower.Tm n}
    (typed : Typing (rules source proofName) context value (typeAt source.types n type)) :
    Typing (rules source proofName) (predicateContext source context type)
      (atPredicate value) (typeAt source.types (n + 1) .prop) := by
  have predicateTyped : Typing (rules source proofName) (predicateContext source context type)
      (.var 0) (typeAt source.types (n + 1) (.arr type .prop)) := by
    simpa only [predicateContext, Ctx.lookup_snoc_zero, typeAt_rename] using
      (Typing.var (R := rules source proofName) (Γ := predicateContext source context type) 0)
  have valueTyped : Typing (rules source proofName) (predicateContext source context type)
      (rename wk value) (typeAt source.types (n + 1) type) := by
    simpa only [typeAt_rename, predicateContext] using
      typed.weaken (extension := typeAt source.types n (.arr type .prop))
  exact application_typed source proofName predicateTyped valueTyped

theorem body_typed {n : Nat} {context : Tower.Ctx n} {type : HOL.Ty Base}
    {left right : Tower.Tm n}
    (leftTyped : Typing (rules source proofName) context left (typeAt source.types n type))
    (rightTyped : Typing (rules source proofName) context right (typeAt source.types n type)) :
    Typing (rules source proofName) (predicateContext source context type)
      (rawImp source (atPredicate left) (atPredicate right)) (typeAt source.types (n + 1) .prop) :=
  FormationSensitiveHOLGenericProofFamily.implication_proposition
    (HOLPredicateEqualitySignature.signature source) proofName
    (atPredicate_typed source proofName leftTyped) (atPredicate_typed source proofName rightTyped)

theorem raw_typed {n : Nat} {context : Tower.Ctx n} {type : HOL.Ty Base}
    {left right : Tower.Tm n}
    (leftTyped : Typing (rules source proofName) context left (typeAt source.types n type))
    (rightTyped : Typing (rules source proofName) context right (typeAt source.types n type)) :
    Typing (rules source proofName) context (raw source type left right)
      (typeAt source.types n .prop) := by
  exact FormationSensitiveHOLGenericProofFamily.universal_lambda_proposition
    (HOLPredicateEqualitySignature.signature source) proofName
    (FormationSensitiveHOLGenericProofFamily.include_typed
      (HOLPredicateEqualitySignature.signature source) proofName
      (typeAt_formed (HOLPredicateEqualitySignature.signature source) (.arr type .prop) context))
    (body_typed source proofName leftTyped rightTyped)

theorem introduction (fresh : source.rules.constantType proofName = none)
    {n : Nat} {context : Tower.Ctx n} {type : HOL.Ty Base}
    {left right : Tower.Tm n} {body : Tower.Tm (n + 2)}
    (leftTyped : Typing (rules source proofName) context left (typeAt source.types n type))
    (rightTyped : Typing (rules source proofName) context right (typeAt source.types n type))
    (bodyTyped : Typing (rules source proofName)
      (.snoc (predicateContext source context type) (proof proofName (atPredicate left))) body
      (rename wk (proof proofName (atPredicate right)))) :
    Typing (rules source proofName) context (.lam (.lam body))
      (proof proofName (raw source type left right)) := by
  have implication := FormationSensitiveHOLGenericProofFamily.implication_intro
    (HOLPredicateEqualitySignature.signature source) proofName fresh
    (atPredicate_typed source proofName leftTyped) (atPredicate_typed source proofName rightTyped) bodyTyped
  exact FormationSensitiveHOLGenericProofFamily.universal_intro
    (HOLPredicateEqualitySignature.signature source) proofName fresh
    (FormationSensitiveHOLGenericProofFamily.include_typed
      (HOLPredicateEqualitySignature.signature source) proofName
      (typeAt_formed (HOLPredicateEqualitySignature.signature source) (.arr type .prop) context))
    (body_typed source proofName leftTyped rightTyped) implication

theorem specialize (fresh : source.rules.constantType proofName = none)
    {n : Nat} {context : Tower.Ctx n} {type : HOL.Ty Base}
    {left right comparison predicate : Tower.Tm n}
    (leftTyped : Typing (rules source proofName) context left (typeAt source.types n type))
    (rightTyped : Typing (rules source proofName) context right (typeAt source.types n type))
    (comparisonTyped : Typing (rules source proofName) context comparison
      (proof proofName (raw source type left right)))
    (predicateTyped : Typing (rules source proofName) context predicate
      (typeAt source.types n (.arr type .prop))) :
    Typing (rules source proofName) context (.app comparison predicate)
      (proof proofName (rawImp source (.app predicate left) (.app predicate right))) := by
  have applied := FormationSensitiveHOLGenericProofFamily.universal_elim
    (HOLPredicateEqualitySignature.signature source) proofName fresh
    (FormationSensitiveHOLGenericProofFamily.include_typed
      (HOLPredicateEqualitySignature.signature source) proofName
      (typeAt_formed (HOLPredicateEqualitySignature.signature source) (.arr type .prop) context))
    (body_typed source proofName leftTyped rightTyped) comparisonTyped predicateTyped
  have instantiate (value : Tower.Tm n) :
      inst0 predicate (atPredicate value) = .app predicate value := by
    have weakened : subst (subst0 predicate) (rename wk value) = value := inst0_rename_wk predicate value
    simp only [atPredicate, inst0, subst, subst0, Fin.cases_zero, weakened]
  have instantiateBody :
      inst0 predicate (rawImp source (atPredicate left) (atPredicate right)) =
        rawImp source (.app predicate left) (.app predicate right) := by
    change subst (subst0 predicate) (rawImp source (atPredicate left) (atPredicate right)) = _
    rw [FormationSensitiveHOLGenericProofFamily.rawImp_subst]
    exact congrArg₂ (rawImp source) (instantiate left) (instantiate right)
  simpa only [instantiateBody] using applied

theorem elimination (fresh : source.rules.constantType proofName = none)
    {n : Nat} {context : Tower.Ctx n} {type : HOL.Ty Base}
    {left right comparison predicate input : Tower.Tm n}
    (leftTyped : Typing (rules source proofName) context left (typeAt source.types n type))
    (rightTyped : Typing (rules source proofName) context right (typeAt source.types n type))
    (comparisonTyped : Typing (rules source proofName) context comparison
      (proof proofName (raw source type left right)))
    (predicateTyped : Typing (rules source proofName) context predicate
      (typeAt source.types n (.arr type .prop)))
    (inputTyped : Typing (rules source proofName) context input (proof proofName (.app predicate left))) :
    Typing (rules source proofName) context (.app (.app comparison predicate) input)
      (proof proofName (.app predicate right)) :=
  FormationSensitiveHOLGenericProofFamily.implication_elim
    (HOLPredicateEqualitySignature.signature source) proofName fresh
    (application_typed source proofName predicateTyped leftTyped)
    (application_typed source proofName predicateTyped rightTyped)
    (specialize source proofName fresh leftTyped rightTyped comparisonTyped predicateTyped) inputTyped

theorem reflexivity (fresh : source.rules.constantType proofName = none)
    {n : Nat} {context : Tower.Ctx n} {type : HOL.Ty Base} {value : Tower.Tm n}
    (typed : Typing (rules source proofName) context value (typeAt source.types n type)) :
    Typing (rules source proofName) context (.lam (.lam (.var 0)))
      (proof proofName (raw source type value value)) :=
  introduction source proofName fresh typed typed (.var 0)

#print axioms introduction
#print axioms specialize
#print axioms elimination
#print axioms reflexivity
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLPredicateEqualityRules
