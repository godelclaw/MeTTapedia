import Mettapedia.OSLF.NativeTypes.Generation.NativeModalDeclarations

/-!
# Native continuation predicates over complete operational event values

A response is a native comprehension of the generated event family sharing its authored program carrier. Its guard
applies the supplied proposition-valued continuation to the event's specified
contractum projection. Formation and substitution use the same full native
syntax and derivation rules as every other generated dependent type.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.NativeModalContinuation

open Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open NativeModalSignature NativeSignature

variable (plan : Plan) (installed : Installation plan.snapshot.language)
    (modal : List (NativeModalHeaders.Header plan))

def eventArguments {n : Nat} (input event : TermExpr (symbols plan installed modal) n) :
    Substitution (symbols plan installed modal) 2 n := extendSubstitution (singletonArgument plan installed modal input) event

def specifiedTarget (index : Fin modal.length) {n : Nat}
    (input event : TermExpr (symbols plan installed modal) n) : TermExpr (symbols plan installed modal) n :=
  .primitive (.inr (.target index)) (eventArguments plan installed modal input event)

def continuationGuard (index : Fin modal.length) {n : Nat}
    (input continuation : TermExpr (symbols plan installed modal) n) : PropExpr (symbols plan installed modal) (n + 1) :=
  .holds (.app (authoredType plan installed modal modal[index].program (n + 1)) .propositions
    (continuation.rename Fin.succ) (specifiedTarget plan installed modal index (input.rename Fin.succ) (.var 0)))

def responseType (index : Fin modal.length) {n : Nat}
    (input continuation : TermExpr (symbols plan installed modal) n) : TypeExpr (symbols plan installed modal) n :=
  .comprehension (eventType plan installed modal index input) (continuationGuard plan installed modal index input continuation)

@[simp] theorem eventType_rename (index : Fin modal.length) {n m : Nat}
    (input : TermExpr (symbols plan installed modal) n) (mapping : Renaming n m) :
    (eventType plan installed modal index input).rename mapping = eventType plan installed modal index (input.rename mapping) := by
  apply congrArg (TypeExpr.family (S := symbols plan installed modal) (.inr (.event index)))
  funext position
  cases position using Fin.cases with
  | zero => rfl
  | succ impossible => exact Fin.elim0 impossible

@[simp] theorem eventType_substitute (index : Fin modal.length) {n m : Nat}
    (input : TermExpr (symbols plan installed modal) n) (substitution : Substitution (symbols plan installed modal) n m) :
    (eventType plan installed modal index input).substitute substitution = eventType plan installed modal index (input.substitute substitution) := by
  apply congrArg (TypeExpr.family (S := symbols plan installed modal) (.inr (.event index)))
  funext position
  cases position using Fin.cases with
  | zero => rfl
  | succ impossible => exact Fin.elim0 impossible

@[simp] theorem specifiedTarget_substitute (index : Fin modal.length) {n m : Nat}
    (input event : TermExpr (symbols plan installed modal) n) (substitution : Substitution (symbols plan installed modal) n m) :
    (specifiedTarget plan installed modal index input event).substitute substitution =
      specifiedTarget plan installed modal index (input.substitute substitution) (event.substitute substitution) := by
  apply congrArg (TermExpr.primitive (S := symbols plan installed modal) (.inr (.target index)))
  funext position
  cases position using Fin.cases with
  | zero => rfl
  | succ position =>
      cases position using Fin.cases with
      | zero => rfl
      | succ impossible => exact Fin.elim0 impossible

@[simp] theorem continuationGuard_substitute (index : Fin modal.length) {n m : Nat}
    (input continuation : TermExpr (symbols plan installed modal) n)
    (substitution : Substitution (symbols plan installed modal) n m) :
    (continuationGuard plan installed modal index input continuation).substitute (liftSubstitution substitution) =
      continuationGuard plan installed modal index (input.substitute substitution) (continuation.substitute substitution) := by
  simp only [continuationGuard, PropExpr.substitute, TermExpr.substitute,
    authoredType_substitute, TermExpr.substitute_weaken, TypeExpr.substitute, specifiedTarget_substitute plan installed modal,
    liftSubstitution_zero]

@[simp] theorem responseType_substitute (index : Fin modal.length) {n m : Nat}
    (input continuation : TermExpr (symbols plan installed modal) n)
    (substitution : Substitution (symbols plan installed modal) n m) :
    (responseType plan installed modal index input continuation).substitute substitution =
      responseType plan installed modal index (input.substitute substitution) (continuation.substitute substitution) := by
  simp only [responseType, TypeExpr.substitute, eventType_substitute, continuationGuard_substitute]

def eventFormationAt (index : Fin modal.length) {n : Nat} {context : ContextExpr (symbols plan installed modal) n}
    {input : TermExpr (symbols plan installed modal) n}
    (formed : Derivation (signature plan installed modal) (.context context))
    (inputTyped : Derivation (signature plan installed modal) (.term context input (inputType plan installed modal index n))) :
    Derivation (signature plan installed modal) (.type context (eventType plan installed modal index input)) :=
  deriveList (.typeFamily context (.inr (.event index)) (singletonArgument plan installed modal input))
    (.cons formed (.cons (inputContextFormed plan installed modal index) (.cons (inputArguments plan installed modal index formed inputTyped) .nil)))

def eventArgumentsFormed (index : Fin modal.length) {n : Nat} {context : ContextExpr (symbols plan installed modal) n}
    {input event : TermExpr (symbols plan installed modal) n}
    (formed : Derivation (signature plan installed modal) (.context context))
    (inputTyped : Derivation (signature plan installed modal) (.term context input (inputType plan installed modal index n)))
    (eventTyped : Derivation (signature plan installed modal) (.term context event (eventType plan installed modal index input))) :
    Derivation (signature plan installed modal) (.substitution context (eventContext plan installed modal index) (eventArguments plan installed modal input event)) := by
  have typed : Derivation (signature plan installed modal) (.term context event
      ((eventType plan installed modal index (.var 0)).substitute (singletonArgument plan installed modal input))) := by
    simpa only [eventType_substitute, TermExpr.substitute, singletonArgument,
      extendSubstitution_zero] using eventTyped
  exact deriveList (.substitutionExtend context (inputContext plan installed modal index) (eventType plan installed modal index (.var 0))
    (singletonArgument plan installed modal input) event)
    (.cons (inputArguments plan installed modal index formed inputTyped) (.cons (eventFormed plan installed modal index) (.cons typed .nil)))

def specifiedTargetFormed (index : Fin modal.length) {n : Nat} {context : ContextExpr (symbols plan installed modal) n}
    {input event : TermExpr (symbols plan installed modal) n}
    (formed : Derivation (signature plan installed modal) (.context context))
    (inputTyped : Derivation (signature plan installed modal) (.term context input (inputType plan installed modal index n)))
    (eventTyped : Derivation (signature plan installed modal) (.term context event (eventType plan installed modal index input))) :
    Derivation (signature plan installed modal) (.term context (specifiedTarget plan installed modal index input event) (authoredType plan installed modal modal[index].program n)) := by
  have tree := deriveList (.primitive context (.inr (.target index)) (eventArguments plan installed modal input event))
    (.cons formed (.cons (eventContextFormed plan installed modal index) (.cons ((headers plan installed modal).termResult (.inr (.target index)))
      (.cons (eventArgumentsFormed plan installed modal index formed inputTyped eventTyped) .nil))))
  change Derivation (signature plan installed modal) (.term context (specifiedTarget plan installed modal index input event)
    ((authoredType plan installed modal modal[index].program 2).substitute (eventArguments plan installed modal input event))) at tree
  rw [authoredType_substitute] at tree
  exact tree

def responseFormation (index : Fin modal.length) {n : Nat} {context : ContextExpr (symbols plan installed modal) n}
    {input continuation : TermExpr (symbols plan installed modal) n}
    (formed : Derivation (signature plan installed modal) (.context context))
    (inputTyped : Derivation (signature plan installed modal) (.term context input (inputType plan installed modal index n)))
    (continuationTyped : Derivation (signature plan installed modal) (.term context continuation
      (.pi (authoredType plan installed modal modal[index].program n) .propositions))) :
    Derivation (signature plan installed modal) (.type context (responseType plan installed modal index input continuation)) := by
  let domain := eventType plan installed modal index input
  let domainTree := eventFormationAt plan installed modal index formed inputTyped
  let extended := deriveList (.contextExtend context domain) (.cons formed (.cons domainTree .nil))
  let weakening := deriveList (.substitutionWeaken context domain) (.cons domainTree .nil)
  have inputThere : Derivation (signature plan installed modal) (.term (.snoc context domain)
      (input.rename Fin.succ) (inputType plan installed modal index (n + 1))) := by
    have tree := deriveList (.substituteTerm (.snoc context domain) context
      (fun position => .var position.succ) input (inputType plan installed modal index n))
      (.cons weakening (.cons inputTyped .nil))
    simpa only [RuleCode.conclusion, TermExpr.substitute_variables, authoredType_substitute, inputType_substitute] using tree
  have continuationThere : Derivation (signature plan installed modal) (.term (.snoc context domain)
      (continuation.rename Fin.succ) (.pi (authoredType plan installed modal modal[index].program (n + 1)) .propositions)) := by
    have tree := deriveList (.substituteTerm (.snoc context domain) context
      (fun position => .var position.succ) continuation (.pi (authoredType plan installed modal modal[index].program n) .propositions))
      (.cons weakening (.cons continuationTyped .nil))
    simpa only [RuleCode.conclusion, TermExpr.substitute_variables, TypeExpr.substitute, authoredType_substitute, inputType_substitute] using tree
  have eventThere : Derivation (signature plan installed modal) (.term (.snoc context domain) (.var 0)
      (eventType plan installed modal index (input.rename Fin.succ))) := by
    have tree := deriveList (.variable (.snoc context domain) 0) (.cons extended .nil)
    simpa only [RuleCode.conclusion, ContextExpr.lookup_zero, domain, eventType_rename plan installed modal] using tree
  let targetTree := specifiedTargetFormed plan installed modal index extended inputThere eventThere
  let patternTree := authoredFormed plan installed modal modal[index].program (.snoc context domain) extended
  let extendedPattern := deriveList (.contextExtend (.snoc context domain) (authoredType plan installed modal modal[index].program (n + 1)))
    (.cons extended (.cons patternTree .nil))
  let propositionTree := deriveList (.propositionType
    (.snoc (.snoc context domain) (authoredType plan installed modal modal[index].program (n + 1)))) (.cons extendedPattern .nil)
  have applied : Derivation (signature plan installed modal) (.term (.snoc context domain)
      (.app (authoredType plan installed modal modal[index].program (n + 1)) .propositions (continuation.rename Fin.succ)
        (specifiedTarget plan installed modal index (input.rename Fin.succ) (.var 0))) .propositions) :=
    deriveList (.application (.snoc context domain) (authoredType plan installed modal modal[index].program (n + 1)) .propositions
      (continuation.rename Fin.succ) (specifiedTarget plan installed modal index (input.rename Fin.succ) (.var 0)))
      (.cons patternTree (.cons propositionTree (.cons continuationThere (.cons targetTree .nil))))
  exact deriveList (.comprehensionFormation context domain (continuationGuard plan installed modal index input continuation))
    (.cons formed (.cons domainTree
      (.cons (deriveList (.holdsFormation (.snoc context domain) _ ) (.cons applied .nil)) .nil)))

def responseCertificate (index : Fin modal.length) {n : Nat} {context : ContextExpr (symbols plan installed modal) n}
    {input continuation : TermExpr (symbols plan installed modal) n}
    (formed : Derivation (signature plan installed modal) (.context context))
    (inputTyped : Derivation (signature plan installed modal) (.term context input (inputType plan installed modal index n)))
    (continuationTyped : Derivation (signature plan installed modal) (.term context continuation
      (.pi (authoredType plan installed modal modal[index].program n) .propositions))) :=
  Certificates.Refinement.erase (responseFormation plan installed modal index formed inputTyped continuationTyped)

theorem responseCertificate_checked (index : Fin modal.length) {n : Nat}
    {context : ContextExpr (symbols plan installed modal) n} {input continuation : TermExpr (symbols plan installed modal) n}
    (formed : Derivation (signature plan installed modal) (.context context))
    (inputTyped : Derivation (signature plan installed modal) (.term context input (inputType plan installed modal index n)))
    (continuationTyped : Derivation (signature plan installed modal) (.term context continuation
      (.pi (authoredType plan installed modal modal[index].program n) .propositions))) :
    Certificates.Refinement.check (responseCertificate plan installed modal index formed inputTyped continuationTyped)
      (.type context (responseType plan installed modal index input continuation)) = true :=
  Certificates.Refinement.check_erase (responseFormation plan installed modal index formed inputTyped continuationTyped)

def responseContext (index : Fin modal.length) : ContextExpr (symbols plan installed modal) 2 :=
  .snoc (inputContext plan installed modal index)
    (.pi (authoredType plan installed modal modal[index].program 1) .propositions)

def responseContextFormed (index : Fin modal.length) :
    Derivation (signature plan installed modal) (.context (responseContext plan installed modal index)) := by
  let inputTree := inputContextFormed plan installed modal index
  let programTree := authoredFormed plan installed modal modal[index].program _ inputTree
  let extended := deriveList (.contextExtend _ _) (.cons inputTree (.cons programTree .nil))
  let predicateTree := deriveList (.propositionType _) (.cons extended .nil)
  let functionTree := deriveList (.piFormation _ _ .propositions)
    (.cons programTree (.cons predicateTree .nil))
  exact deriveList (.contextExtend _ _) (.cons inputTree (.cons functionTree .nil))

def responseInputFormed (index : Fin modal.length) :
    Derivation (signature plan installed modal)
      (.term (responseContext plan installed modal index) (.var 1)
        (inputType plan installed modal index 2)) := by
  have tree := deriveList (.variable (responseContext plan installed modal index) 1)
    (.cons (responseContextFormed plan installed modal index) .nil)
  have lookup : (responseContext plan installed modal index).lookup (1 : Fin 2) =
      inputType plan installed modal index 2 := by
    change ((inputType plan installed modal index 0).rename Fin.succ).rename Fin.succ = _
    rw [inputType_rename, inputType_rename]
  simpa only [RuleCode.conclusion, lookup] using tree

def responsePredicateFormed (index : Fin modal.length) :
    Derivation (signature plan installed modal)
      (.term (responseContext plan installed modal index) (.var 0)
        (.pi (authoredType plan installed modal modal[index].program 2) .propositions)) := by
  have tree := deriveList (.variable (responseContext plan installed modal index) 0)
    (.cons (responseContextFormed plan installed modal index) .nil)
  simpa only [RuleCode.conclusion, responseContext, ContextExpr.lookup_zero,
    TypeExpr.rename, authoredType_rename] using tree

def genericResponseFormation (index : Fin modal.length) :
    Derivation (signature plan installed modal)
      (.type (responseContext plan installed modal index)
        (responseType plan installed modal index (.var 1) (.var 0))) :=
  responseFormation plan installed modal index
    (responseContextFormed plan installed modal index)
    (responseInputFormed plan installed modal index)
    (responsePredicateFormed plan installed modal index)

theorem genericResponse_checked (index : Fin modal.length) :
    Certificates.Refinement.check
      (Certificates.Refinement.erase (genericResponseFormation plan installed modal index))
      (.type (responseContext plan installed modal index)
        (responseType plan installed modal index (.var 1) (.var 0))) = true :=
  Certificates.Refinement.check_erase _

end Mettapedia.OSLF.NativeTypes.Generation.NativeModalContinuation

