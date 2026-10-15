import Mettapedia.OSLF.NativeTypes.Modal.NativeEventDeclarations

/-!
# Native continuation predicates over complete operational event values

A response is a native comprehension of the generated event family. Its guard
applies the supplied proposition-valued continuation to the event's specified
contractum projection. Formation and substitution use the same full native
syntax and derivation rules as every other generated dependent type.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.NativeContinuation

open Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open NativeEventDeclarations

variable {plan : Plan}

def eventArguments {n : Nat} (input event : TermExpr (symbols plan) n) :
    Substitution (symbols plan) 2 n := extendSubstitution (singletonArgument input) event

def specifiedTarget (index : Index plan) {n : Nat}
    (input event : TermExpr (symbols plan) n) : TermExpr (symbols plan) n :=
  .primitive (.target index) (eventArguments input event)

def continuationGuard (index : Index plan) {n : Nat}
    (input continuation : TermExpr (symbols plan) n) : PropExpr (symbols plan) (n + 1) :=
  .holds (.app (carrierType .pattern (n + 1)) .propositions
    (continuation.rename Fin.succ) (specifiedTarget index (input.rename Fin.succ) (.var 0)))

def responseType (index : Index plan) {n : Nat}
    (input continuation : TermExpr (symbols plan) n) : TypeExpr (symbols plan) n :=
  .comprehension (eventType index input) (continuationGuard index input continuation)

@[simp] theorem eventType_rename (index : Index plan) {n m : Nat}
    (input : TermExpr (symbols plan) n) (mapping : Renaming n m) :
    (eventType index input).rename mapping = eventType index (input.rename mapping) := by
  apply congrArg (TypeExpr.family (S := symbols plan) (.event index))
  funext position
  cases position using Fin.cases with
  | zero => rfl
  | succ impossible => exact Fin.elim0 impossible

@[simp] theorem eventType_substitute (index : Index plan) {n m : Nat}
    (input : TermExpr (symbols plan) n) (substitution : Substitution (symbols plan) n m) :
    (eventType index input).substitute substitution = eventType index (input.substitute substitution) := by
  apply congrArg (TypeExpr.family (S := symbols plan) (.event index))
  funext position
  cases position using Fin.cases with
  | zero => rfl
  | succ impossible => exact Fin.elim0 impossible

@[simp] theorem specifiedTarget_substitute (index : Index plan) {n m : Nat}
    (input event : TermExpr (symbols plan) n) (substitution : Substitution (symbols plan) n m) :
    (specifiedTarget index input event).substitute substitution =
      specifiedTarget index (input.substitute substitution) (event.substitute substitution) := by
  apply congrArg (TermExpr.primitive (S := symbols plan) (.target index))
  funext position
  cases position using Fin.cases with
  | zero => rfl
  | succ position =>
      cases position using Fin.cases with
      | zero => rfl
      | succ impossible => exact Fin.elim0 impossible

@[simp] theorem continuationGuard_substitute (index : Index plan) {n m : Nat}
    (input continuation : TermExpr (symbols plan) n)
    (substitution : Substitution (symbols plan) n m) :
    (continuationGuard index input continuation).substitute (liftSubstitution substitution) =
      continuationGuard index (input.substitute substitution) (continuation.substitute substitution) := by
  simp only [continuationGuard, PropExpr.substitute, TermExpr.substitute,
    carrierType_substitute, TermExpr.substitute_weaken, TypeExpr.substitute, specifiedTarget_substitute,
    liftSubstitution_zero]

@[simp] theorem responseType_substitute (index : Index plan) {n m : Nat}
    (input continuation : TermExpr (symbols plan) n)
    (substitution : Substitution (symbols plan) n m) :
    (responseType index input continuation).substitute substitution =
      responseType index (input.substitute substitution) (continuation.substitute substitution) := by
  simp only [responseType, TypeExpr.substitute, eventType_substitute, continuationGuard_substitute]

def eventFormationAt (index : Index plan) {n : Nat} {context : ContextExpr (symbols plan) n}
    {input : TermExpr (symbols plan) n}
    (formed : Derivation (signature plan) (.context context))
    (inputTyped : Derivation (signature plan) (.term context input (carrierType .input n))) :
    Derivation (signature plan) (.type context (eventType index input)) :=
  deriveList (.typeFamily context (.event index) (singletonArgument input))
    (.cons formed (.cons inputContextFormed (.cons (inputArguments formed inputTyped) .nil)))

def eventArgumentsFormed (index : Index plan) {n : Nat} {context : ContextExpr (symbols plan) n}
    {input event : TermExpr (symbols plan) n}
    (formed : Derivation (signature plan) (.context context))
    (inputTyped : Derivation (signature plan) (.term context input (carrierType .input n)))
    (eventTyped : Derivation (signature plan) (.term context event (eventType index input))) :
    Derivation (signature plan) (.substitution context (eventContext index) (eventArguments input event)) := by
  have typed : Derivation (signature plan) (.term context event
      ((eventType index (.var 0)).substitute (singletonArgument input))) := by
    simpa only [eventType_substitute, TermExpr.substitute, singletonArgument,
      extendSubstitution_zero] using eventTyped
  exact deriveList (.substitutionExtend context inputContext (eventType index (.var 0))
    (singletonArgument input) event)
    (.cons (inputArguments formed inputTyped) (.cons (eventFormation index) (.cons typed .nil)))

def specifiedTargetFormed (index : Index plan) {n : Nat} {context : ContextExpr (symbols plan) n}
    {input event : TermExpr (symbols plan) n}
    (formed : Derivation (signature plan) (.context context))
    (inputTyped : Derivation (signature plan) (.term context input (carrierType .input n)))
    (eventTyped : Derivation (signature plan) (.term context event (eventType index input))) :
    Derivation (signature plan) (.term context (specifiedTarget index input event) (carrierType .pattern n)) := by
  have tree := deriveList (.primitive context (.target index) (eventArguments input event))
    (.cons formed (.cons (eventContextFormed index) (.cons ((headers plan).termResult (.target index))
      (.cons (eventArgumentsFormed index formed inputTyped eventTyped) .nil))))
  change Derivation (signature plan) (.term context (specifiedTarget index input event)
    ((carrierType .pattern 2).substitute (eventArguments input event))) at tree
  rw [carrierType_substitute] at tree
  exact tree

def responseFormation (index : Index plan) {n : Nat} {context : ContextExpr (symbols plan) n}
    {input continuation : TermExpr (symbols plan) n}
    (formed : Derivation (signature plan) (.context context))
    (inputTyped : Derivation (signature plan) (.term context input (carrierType .input n)))
    (continuationTyped : Derivation (signature plan) (.term context continuation
      (.pi (carrierType .pattern n) .propositions))) :
    Derivation (signature plan) (.type context (responseType index input continuation)) := by
  let domain := eventType index input
  let domainTree := eventFormationAt index formed inputTyped
  let extended := deriveList (.contextExtend context domain) (.cons formed (.cons domainTree .nil))
  let weakening := deriveList (.substitutionWeaken context domain) (.cons domainTree .nil)
  have inputThere : Derivation (signature plan) (.term (.snoc context domain)
      (input.rename Fin.succ) (carrierType .input (n + 1))) := by
    have tree := deriveList (.substituteTerm (.snoc context domain) context
      (fun position => .var position.succ) input (carrierType .input n))
      (.cons weakening (.cons inputTyped .nil))
    simpa only [RuleCode.conclusion, TermExpr.substitute_variables, carrierType_substitute] using tree
  have continuationThere : Derivation (signature plan) (.term (.snoc context domain)
      (continuation.rename Fin.succ) (.pi (carrierType .pattern (n + 1)) .propositions)) := by
    have tree := deriveList (.substituteTerm (.snoc context domain) context
      (fun position => .var position.succ) continuation (.pi (carrierType .pattern n) .propositions))
      (.cons weakening (.cons continuationTyped .nil))
    simpa only [RuleCode.conclusion, TermExpr.substitute_variables, TypeExpr.substitute, carrierType_substitute] using tree
  have eventThere : Derivation (signature plan) (.term (.snoc context domain) (.var 0)
      (eventType index (input.rename Fin.succ))) := by
    have tree := deriveList (.variable (.snoc context domain) 0) (.cons extended .nil)
    simpa only [RuleCode.conclusion, ContextExpr.lookup_zero, domain, eventType_rename] using tree
  let targetTree := specifiedTargetFormed index extended inputThere eventThere
  let patternTree := carrierFormed .pattern extended
  let extendedPattern := deriveList (.contextExtend (.snoc context domain) (carrierType .pattern (n + 1)))
    (.cons extended (.cons patternTree .nil))
  let propositionTree := deriveList (.propositionType
    (.snoc (.snoc context domain) (carrierType .pattern (n + 1)))) (.cons extendedPattern .nil)
  have applied : Derivation (signature plan) (.term (.snoc context domain)
      (.app (carrierType .pattern (n + 1)) .propositions (continuation.rename Fin.succ)
        (specifiedTarget index (input.rename Fin.succ) (.var 0))) .propositions) :=
    deriveList (.application (.snoc context domain) (carrierType .pattern (n + 1)) .propositions
      (continuation.rename Fin.succ) (specifiedTarget index (input.rename Fin.succ) (.var 0)))
      (.cons patternTree (.cons propositionTree (.cons continuationThere (.cons targetTree .nil))))
  exact deriveList (.comprehensionFormation context domain (continuationGuard index input continuation))
    (.cons formed (.cons domainTree
      (.cons (deriveList (.holdsFormation (.snoc context domain) _ ) (.cons applied .nil)) .nil)))

def responseCertificate (index : Index plan) {n : Nat} {context : ContextExpr (symbols plan) n}
    {input continuation : TermExpr (symbols plan) n}
    (formed : Derivation (signature plan) (.context context))
    (inputTyped : Derivation (signature plan) (.term context input (carrierType .input n)))
    (continuationTyped : Derivation (signature plan) (.term context continuation
      (.pi (carrierType .pattern n) .propositions))) :=
  Certificates.Refinement.erase (responseFormation index formed inputTyped continuationTyped)

theorem responseCertificate_checked (index : Index plan) {n : Nat}
    {context : ContextExpr (symbols plan) n} {input continuation : TermExpr (symbols plan) n}
    (formed : Derivation (signature plan) (.context context))
    (inputTyped : Derivation (signature plan) (.term context input (carrierType .input n)))
    (continuationTyped : Derivation (signature plan) (.term context continuation
      (.pi (carrierType .pattern n) .propositions))) :
    Certificates.Refinement.check (responseCertificate index formed inputTyped continuationTyped)
      (.type context (responseType index input continuation)) = true :=
  Certificates.Refinement.check_erase (responseFormation index formed inputTyped continuationTyped)

end Mettapedia.OSLF.NativeTypes.Modal.NativeContinuation
