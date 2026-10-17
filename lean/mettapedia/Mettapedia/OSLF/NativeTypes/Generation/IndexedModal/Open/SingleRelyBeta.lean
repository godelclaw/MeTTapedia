import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.SingleRelyParameters

/-! # Native beta computation of the generated constant continuation -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.SingleRelyBeta

open _root_.CategoryTheory
open Mettapedia.TypeTheory Calculi.NativeDependent.Refinement
open Mettapedia.OSLF.NativeTypes.Semantics
open Presheaf CubeEnrichment CubeNativeDeclarations
open Mettapedia.OSLF.Framework.ModalHypercube (HSort)

universe u

private theorem newestTerm_cancellation {S : Symbols.{u}} {n : Nat}
    (body : TermExpr S (n + 1)) :
    (body.rename (liftRenaming (Fin.succ : Renaming n (n + 1)))).substitute
      (instantiate (.var 0)) = body := by
  rw [TermExpr.substitute_rename]
  have square : (instantiate (.var 0 : TermExpr S (n + 1))) ∘ liftRenaming Fin.succ =
      (TermExpr.var : Substitution S (n + 1) (n + 1)) := by
    funext position
    cases position using Fin.cases <;> rfl
  rw [square, TermExpr.substitute_identity]

private structure Opening {S : Symbols.{u}} (theory : Signature S) {n : Nat}
    (context : ContextExpr S n) (domain : TypeExpr S n) (body : TypeExpr S (n + 1)) where
  domainThere : Derivation theory (.type (.snoc context domain) (domain.rename Fin.succ))
  bodyThere : Derivation theory
    (.type (.snoc (.snoc context domain) (domain.rename Fin.succ)) (body.rename (liftRenaming Fin.succ)))
  weakening : Derivation theory (.substitution (.snoc context domain) context (fun position => .var position.succ))
  lifted : Derivation theory
    (.substitution (.snoc (.snoc context domain) (domain.rename Fin.succ)) (.snoc context domain)
      (fun position => .var (liftRenaming Fin.succ position)))
  newest : Derivation theory (.term (.snoc context domain) (.var 0) (domain.rename Fin.succ))

private def opening {S : Symbols.{u}} {theory : Signature S} {n : Nat}
    {context : ContextExpr S n} {domain : TypeExpr S n} {body : TypeExpr S (n + 1)}
    (formed : Derivation theory (.context context))
    (domainFormed : Derivation theory (.type context domain))
    (bodyFormed : Derivation theory (.type (.snoc context domain) body)) : Opening theory context domain body := by
  let weakened := deriveList (.substitutionWeaken context domain) (.cons domainFormed .nil)
  have domainThere : Derivation theory (.type (.snoc context domain) (domain.rename Fin.succ)) := by
    simpa only [RuleCode.conclusion, TypeExpr.substitute_variables] using
      deriveList (.substituteType (.snoc context domain) context (fun position => .var position.succ) domain)
        (.cons weakened (.cons domainFormed .nil))
  have lifted : Derivation theory
      (.substitution (.snoc (.snoc context domain) (domain.rename Fin.succ)) (.snoc context domain)
        (fun position => .var (liftRenaming Fin.succ position))) := by
    simpa only [RuleCode.conclusion, TypeExpr.substitute_variables, liftSubstitution_variables] using
      deriveList (.substitutionLift (.snoc context domain) context domain (fun position => .var position.succ))
        (.cons weakened (.cons domainFormed .nil))
  have bodyThere : Derivation theory
      (.type (.snoc (.snoc context domain) (domain.rename Fin.succ)) (body.rename (liftRenaming Fin.succ))) := by
    simpa only [RuleCode.conclusion, TypeExpr.substitute_variables] using
      deriveList (.substituteType _ _ (fun position => .var (liftRenaming Fin.succ position)) body)
        (.cons lifted (.cons bodyFormed .nil))
  have newest : Derivation theory (.term (.snoc context domain) (.var 0) (domain.rename Fin.succ)) := by
    simpa only [RuleCode.conclusion, ContextExpr.lookup_zero] using
      deriveList (.variable (.snoc context domain) 0)
        (.cons (extendContextFormed formed domainFormed) .nil)
  exact ⟨domainThere, bodyThere, weakened, lifted, newest⟩

private def applyVariableBeta {S : Symbols.{u}} {theory : Signature S} {n : Nat}
    {context : ContextExpr S n} {domain : TypeExpr S n} {body : TypeExpr S (n + 1)}
    {term : TermExpr S (n + 1)}
    (formed : Derivation theory (.context context))
    (domainFormed : Derivation theory (.type context domain))
    (bodyFormed : Derivation theory (.type (.snoc context domain) body))
    (typed : Derivation theory (.term (.snoc context domain) term body)) :
    Derivation theory (.termEq (.snoc context domain)
      (applyVariableTerm domain body (.lam domain body term)) term body) := by
  let opened := opening formed domainFormed bodyFormed
  have termThere : Derivation theory
      (.term (.snoc (.snoc context domain) (domain.rename Fin.succ))
        (term.rename (liftRenaming Fin.succ)) (body.rename (liftRenaming Fin.succ))) := by
    simpa only [RuleCode.conclusion, TypeExpr.substitute_variables, TermExpr.substitute_variables] using
      deriveList (.substituteTerm _ _ (fun position => .var (liftRenaming Fin.succ position)) term body)
        (.cons opened.lifted (.cons typed .nil))
  simpa only [RuleCode.conclusion, applyVariableTerm, TermExpr.rename,
    newestTerm_cancellation, newestVariable_cancellation] using
    deriveList (.piBeta (.snoc context domain) (domain.rename Fin.succ)
      (body.rename (liftRenaming Fin.succ)) (term.rename (liftRenaming Fin.succ)) (.var 0))
      (.cons opened.domainThere (.cons opened.bodyThere (.cons termThere (.cons opened.newest .nil))))

private def applyVariableCongruence {S : Symbols.{u}} {theory : Signature S} {n : Nat}
    {context : ContextExpr S n} {domain : TypeExpr S n} {body : TypeExpr S (n + 1)}
    {first second : TermExpr S n}
    (formed : Derivation theory (.context context))
    (domainFormed : Derivation theory (.type context domain))
    (bodyFormed : Derivation theory (.type (.snoc context domain) body))
    (same : Derivation theory (.termEq context first second (.pi domain body))) :
    Derivation theory (.termEq (.snoc context domain)
      (applyVariableTerm domain body first) (applyVariableTerm domain body second) body) := by
  let opened := opening formed domainFormed bodyFormed
  have there : Derivation theory (.termEq (.snoc context domain)
      (first.rename Fin.succ) (second.rename Fin.succ)
      (.pi (domain.rename Fin.succ) (body.rename (liftRenaming Fin.succ)))) := by
    simpa only [RuleCode.conclusion, TypeExpr.substitute_variables, TermExpr.substitute_variables, TypeExpr.rename] using
      deriveList (.substituteTermEquality (.snoc context domain) context
        (fun position => .var position.succ) first second (.pi domain body))
        (.cons opened.weakening (.cons same .nil))
  let newest := deriveList (.termReflexivity (.snoc context domain) (.var 0) (domain.rename Fin.succ))
    (.cons opened.newest .nil)
  simpa only [RuleCode.conclusion, applyVariableTerm, newestVariable_cancellation] using
    deriveList (.applicationCongruence (.snoc context domain) (domain.rename Fin.succ)
      (body.rename (liftRenaming Fin.succ)) (first.rename Fin.succ) (second.rename Fin.succ) (.var 0) (.var 0))
      (.cons opened.domainThere (.cons opened.bodyThere (.cons there (.cons newest .nil))))

variable {D : CubeEnrichment.Signature} (vertex : Vertex D)
    (rely target focus : D.Carrier) (kind sort : HSort)
open SingleRelyParameters

abbrev inner : TermExpr (symbols D) 3 :=
  .lam (membershipType rely kind) (certifiedCode target sort 4) (.var 2)

abbrev firstApplication : TermExpr (symbols D) 3 :=
  applyVariableTerm (valueType rely) (.pi (membershipType rely kind) (certifiedCode target sort 4))
    (constantContinuation rely target kind sort)

abbrev secondApplication : TermExpr (symbols D) 4 :=
  applyVariableTerm (membershipType rely kind) (certifiedCode target sort 4)
    (firstApplication rely target kind sort)

def target_beta : Derivation (Theory vertex)
    (.termEq (withEvidence rely target kind sort)
      (secondApplication rely target kind sort) (.var 2) (certifiedCode target sort 4)) := by
  let result := certifiedFormed vertex target sort (evidenceFormed vertex rely target kind sort)
  let innerTyped := deriveList (.lambda (withValue rely target kind sort) (membershipType rely kind)
    (certifiedCode target sort 4) (.var 2))
    (.cons (membershipFormed vertex rely target kind sort) (.cons result (.cons (targetThere vertex rely target kind sort) .nil)))
  let body := deriveList (.piFormation (withValue rely target kind sort)
    (membershipType rely kind) (certifiedCode target sort 4))
    (.cons (membershipFormed vertex rely target kind sort) (.cons result .nil))
  have first := applyVariableBeta (pairFormed vertex rely target kind sort)
    (valueFormed vertex rely target kind sort) body innerTyped
  have under := applyVariableCongruence
    (extendFormed vertex (pairFormed vertex rely target kind sort) (valueFormed vertex rely target kind sort))
    (membershipFormed vertex rely target kind sort) result first
  have second := applyVariableBeta
    (extendFormed vertex (pairFormed vertex rely target kind sort) (valueFormed vertex rely target kind sort))
    (membershipFormed vertex rely target kind sort) result (targetThere vertex rely target kind sort)
  exact deriveList (.termTransitivity (withEvidence rely target kind sort)
    (secondApplication rely target kind sort)
    (applyVariableTerm (membershipType rely kind) (certifiedCode target sort 4) (inner rely target kind sort))
    (.var 2) (certifiedCode target sort 4)) (.cons under (.cons second .nil))

def resizeContext {n m : Nat} (same : n = m) (context : ContextExpr (symbols D) n) :
    ContextExpr (symbols D) m := cast (congrArg (ContextExpr (symbols D)) same) context

def resizeTerm {n m : Nat} (same : n = m) (term : TermExpr (symbols D) n) :
    TermExpr (symbols D) m := cast (congrArg (TermExpr (symbols D)) same) term

theorem resizeTerm_substitute {n m k : Nat} (same : n = m) (term : TermExpr (symbols D) n)
    (mapping : Substitution (symbols D) m k) :
    (resizeTerm same term).substitute mapping =
      term.substitute (fun position => mapping (Fin.cast same position)) := by
  cases same
  rfl

abbrev generatedSyntax := ContinuationSyntax.generated vertex (interface rely target focus kind sort)

theorem requestSize : (generatedSyntax vertex rely target focus kind sort).size = 4 := by
  rw [ContinuationSyntax.generated_size]
  rfl

abbrev singleArgument : D.Carrier × TermExpr (symbols D)
    (prefixSize (interface rely target focus kind sort)) :=
  (rely, classifierValue rely kind (.var ⟨0, by change 0 < 1; decide⟩))

theorem relyArguments_single : relyArguments (D := D) (interface rely target focus kind sort) =
    [singleArgument rely target focus kind sort] := by
  apply List.ext_getElem
  · simp only [relyArguments, List.length_ofFn, interface, List.length_cons, List.length_nil]
  · intro position left right
    have zero : position = 0 := by
      have small : position < 1 := by simpa only [List.length_cons, List.length_nil] using right
      omega
    subst position
    have entry := ContinuationSemantics.relyEntry (D := D) (interface rely target focus kind sort)
      ⟨0, by change 0 < 1; decide⟩
    exact entry

def normalizedContext : ContextExpr (symbols D) 4 :=
  resizeContext (requestSize vertex rely target focus kind sort)
    (generatedSyntax vertex rely target focus kind sort).scope

abbrev originalMembership : TypeExpr (symbols D) 3 :=
  typingType rely (.var 0) (classifierValue rely kind (.var 2))

abbrev originalContext : ContextExpr (symbols D) 4 :=
  .snoc (.snoc (parameters (D := D) (interface rely target focus kind sort)) (codeType rely 2))
    (originalMembership rely kind)

private theorem singletonScope {n m : Nat} {context : ContextExpr (symbols D) m}
    (target : D.Carrier) (sort : HSort) (entries : List (D.Carrier × TermExpr (symbols D) n))
    (entry : D.Carrier × TermExpr (symbols D) n) (single : entries = [entry])
    (mapping : Substitution (symbols D) n m)
    (formed : Derivation (Theory vertex) (.context context))
    (classifiers : ∀ position : Fin entries.length, Derivation (Theory vertex)
      (.term context (entries[position].2.substitute mapping) (codeType entries[position].1 m)))
    (function : TermExpr (symbols D) m)
    (typed : Derivation (Theory vertex) (.term context function (continuationAt target sort entries mapping))) :
    HEq (ContinuationSyntax.openAll vertex target sort entries mapping formed classifiers function typed).scope
      (ContinuationSyntax.nextContext context entry mapping) := by
  subst entries
  rw [ContinuationSyntax.openAll]
  dsimp only
  simp only [ContinuationSyntax.prepend]
  rw [ContinuationSyntax.openAll]

private theorem singletonOutput {n m : Nat} {context : ContextExpr (symbols D) m}
    (target : D.Carrier) (sort : HSort) (entries : List (D.Carrier × TermExpr (symbols D) n))
    (entry : D.Carrier × TermExpr (symbols D) n) (single : entries = [entry])
    (mapping : Substitution (symbols D) n m)
    (formed : Derivation (Theory vertex) (.context context))
    (classifiers : ∀ position : Fin entries.length, Derivation (Theory vertex)
      (.term context (entries[position].2.substitute mapping) (codeType entries[position].1 m)))
    (function : TermExpr (symbols D) m)
    (typed : Derivation (Theory vertex) (.term context function (continuationAt target sort entries mapping))) :
    HEq (ContinuationSyntax.openAll vertex target sort entries mapping formed classifiers function typed).output
      (applyVariableTerm (ContinuationSyntax.membership entry mapping) (certifiedCode target sort (m + 2))
        (applyVariableTerm (codeType entry.1 m)
          (.pi (ContinuationSyntax.membership entry mapping) (certifiedCode target sort (m + 2))) function)) := by
  subst entries
  rw [ContinuationSyntax.openAll]
  dsimp only
  simp only [ContinuationSyntax.prepend]
  rw [ContinuationSyntax.openAll]
  dsimp only
  rfl

private theorem singletonProjection {n m : Nat} {context : ContextExpr (symbols D) m}
    (target : D.Carrier) (sort : HSort) (entries : List (D.Carrier × TermExpr (symbols D) n))
    (entry : D.Carrier × TermExpr (symbols D) n) (single : entries = [entry])
    (mapping : Substitution (symbols D) n m)
    (formed : Derivation (Theory vertex) (.context context))
    (classifiers : ∀ position : Fin entries.length, Derivation (Theory vertex)
      (.term context (entries[position].2.substitute mapping) (codeType entries[position].1 m)))
    (function : TermExpr (symbols D) m)
    (typed : Derivation (Theory vertex) (.term context function (continuationAt target sort entries mapping)))
    (position : Fin m) :
    HEq ((ContinuationSyntax.openAll vertex target sort entries mapping formed classifiers function typed).projection position)
      (.var position.succ.succ : TermExpr (symbols D) (m + 2)) := by
  subst entries
  rw [ContinuationSyntax.openAll]
  dsimp only
  simp only [ContinuationSyntax.prepend]
  rw [ContinuationSyntax.openAll]
  dsimp only
  rfl

private theorem singletonValue {n m : Nat} {context : ContextExpr (symbols D) m}
    (target : D.Carrier) (sort : HSort) (entries : List (D.Carrier × TermExpr (symbols D) n))
    (entry : D.Carrier × TermExpr (symbols D) n) (single : entries = [entry])
    (mapping : Substitution (symbols D) n m)
    (formed : Derivation (Theory vertex) (.context context))
    (classifiers : ∀ position : Fin entries.length, Derivation (Theory vertex)
      (.term context (entries[position].2.substitute mapping) (codeType entries[position].1 m)))
    (function : TermExpr (symbols D) m)
    (typed : Derivation (Theory vertex) (.term context function (continuationAt target sort entries mapping)))
    (position : Fin entries.length) :
    HEq ((ContinuationSyntax.openAll vertex target sort entries mapping formed classifiers function typed).values position)
      (.var 1 : TermExpr (symbols D) (m + 2)) := by
  subst entries
  have zero : position = 0 := Fin.eq_zero position
  subst position
  rw [ContinuationSyntax.openAll]
  dsimp only
  simp only [ContinuationSyntax.prepend, Fin.cons_zero]
  rw [ContinuationSyntax.openAll]

private theorem resizeContext_eq {n m : Nat} (same : n = m)
    (first : ContextExpr (symbols D) n) (second : ContextExpr (symbols D) m)
    (equal : HEq first second) : resizeContext same first = second := by
  cases same
  exact eq_of_heq equal

private theorem resizeTerm_eq {n m : Nat} (same : n = m)
    (first : TermExpr (symbols D) n) (second : TermExpr (symbols D) m)
    (equal : HEq first second) : resizeTerm same first = second := by
  cases same
  exact eq_of_heq equal

theorem generatedMembership_eq :
    ContinuationSyntax.membership (singleArgument (D := D) rely target focus kind sort)
      (ContinuationSyntax.initialMapping (interface rely target focus kind sort)) = originalMembership rely kind := by
  change typingType rely (.var 0)
    (((classifierValue rely kind (.var 0 : TermExpr (symbols D) 1)).substitute
      (fun position : Fin 1 => (.var position.succ : TermExpr (symbols D) 2))).rename Fin.succ) = _
  rw [IndexSyntax.classifierValue_substitute, classifierValue_rename]
  rfl

theorem request_scope_heq : HEq (generatedSyntax vertex rely target focus kind sort).scope
    (originalContext rely target focus kind sort) := by
  have same := singletonScope vertex target sort
    (relyArguments (D := D) (interface rely target focus kind sort))
    (singleArgument rely target focus kind sort) (relyArguments_single rely target focus kind sort)
    (ContinuationSyntax.initialMapping (D := D) (interface rely target focus kind sort))
    (parametersFormed vertex (interface rely target focus kind sort))
    (ContinuationSyntax.initialClassifiers vertex (interface rely target focus kind sort))
    (.var (ContinuationSyntax.targetPosition (D := D) (interface rely target focus kind sort)))
    (ContinuationSyntax.initialFunction vertex (interface rely target focus kind sort))
  unfold ContinuationSyntax.nextContext at same
  rw [generatedMembership_eq] at same
  exact same

theorem normalizedContext_eq : normalizedContext vertex rely target focus kind sort =
    originalContext rely target focus kind sort :=
  resizeContext_eq (requestSize vertex rely target focus kind sort) _ _
    (request_scope_heq vertex rely target focus kind sort)

def normalizedOutput : TermExpr (symbols D) 4 :=
  resizeTerm (requestSize vertex rely target focus kind sort)
    (generatedSyntax vertex rely target focus kind sort).output

abbrev originalFirst : TermExpr (symbols D) 3 :=
  applyVariableTerm (codeType rely 2)
    (.pi (originalMembership rely kind) (certifiedCode target sort 4)) (.var 0)

abbrev originalSecond : TermExpr (symbols D) 4 :=
  applyVariableTerm (originalMembership rely kind) (certifiedCode target sort 4)
    (originalFirst rely target kind sort)

theorem request_output_heq : HEq (generatedSyntax vertex rely target focus kind sort).output
    (originalSecond rely target kind sort) := by
  have same := singletonOutput vertex target sort
    (relyArguments (D := D) (interface rely target focus kind sort))
    (singleArgument rely target focus kind sort) (relyArguments_single rely target focus kind sort)
    (ContinuationSyntax.initialMapping (D := D) (interface rely target focus kind sort))
    (parametersFormed vertex (interface rely target focus kind sort))
    (ContinuationSyntax.initialClassifiers vertex (interface rely target focus kind sort))
    (.var (ContinuationSyntax.targetPosition (D := D) (interface rely target focus kind sort)))
    (ContinuationSyntax.initialFunction vertex (interface rely target focus kind sort))
  rw [generatedMembership_eq] at same
  exact same

theorem normalizedOutput_eq : normalizedOutput vertex rely target focus kind sort =
    originalSecond rely target kind sort :=
  resizeTerm_eq (requestSize vertex rely target focus kind sort) _ _
    (request_output_heq vertex rely target focus kind sort)

def normalizedProjection (position : Fin 2) : TermExpr (symbols D) 4 :=
  resizeTerm (requestSize vertex rely target focus kind sort)
    ((generatedSyntax vertex rely target focus kind sort).projection position)

theorem normalizedProjection_eq (position : Fin 2) :
    normalizedProjection vertex rely target focus kind sort position = .var position.succ.succ := by
  apply resizeTerm_eq
  exact singletonProjection vertex target sort
    (relyArguments (D := D) (interface rely target focus kind sort))
    (singleArgument rely target focus kind sort) (relyArguments_single rely target focus kind sort)
    (ContinuationSyntax.initialMapping (D := D) (interface rely target focus kind sort))
    (parametersFormed vertex (interface rely target focus kind sort))
    (ContinuationSyntax.initialClassifiers vertex (interface rely target focus kind sort))
    (.var (ContinuationSyntax.targetPosition (D := D) (interface rely target focus kind sort)))
    (ContinuationSyntax.initialFunction vertex (interface rely target focus kind sort)) position

theorem normalizedRely_eq :
    resizeTerm (requestSize vertex rely target focus kind sort)
      (ContinuationSemantics.relyValueTerm vertex (interface rely target focus kind sort) 0) = .var 1 := by
  apply resizeTerm_eq
  exact singletonValue vertex target sort
    (relyArguments (D := D) (interface rely target focus kind sort))
    (singleArgument rely target focus kind sort) (relyArguments_single rely target focus kind sort)
    (ContinuationSyntax.initialMapping (D := D) (interface rely target focus kind sort))
    (parametersFormed vertex (interface rely target focus kind sort))
    (ContinuationSyntax.initialClassifiers vertex (interface rely target focus kind sort))
    (.var (ContinuationSyntax.targetPosition (D := D) (interface rely target focus kind sort)))
    (ContinuationSyntax.initialFunction vertex (interface rely target focus kind sort))
    (ContinuationSemantics.relyPosition (interface rely target focus kind sort) 0)

abbrev requestMapping : Substitution (symbols D)
    (generatedSyntax vertex rely target focus kind sort).size 4 :=
  fun position => (liftSubstitution (liftSubstitution (parameterMapping rely target focus kind sort)))
    (Fin.cast (requestSize vertex rely target focus kind sort) position)

theorem parameterMapping_explicit :
    (parameterMapping (D := D) rely target focus kind sort : Substitution (symbols D) 2 2) =
      (Fin.cases (constantContinuation rely target kind sort) (fun _ => (.var 1 : TermExpr (symbols D) 2)) : Substitution (symbols D) 2 2) := by
  funext position
  cases position using Fin.cases with
  | zero => rfl
  | succ position =>
      change Fin 1 at position
      have zero : position = 0 := Fin.eq_zero position
      cases zero
      rfl

theorem output_substitute :
    (generatedSyntax vertex rely target focus kind sort).output.substitute
      (requestMapping vertex rely target focus kind sort) = secondApplication rely target kind sort := by
  change (generatedSyntax vertex rely target focus kind sort).output.substitute
    (fun position => (liftSubstitution (liftSubstitution (parameterMapping rely target focus kind sort)))
      (Fin.cast (requestSize vertex rely target focus kind sort) position)) = _
  rw [← resizeTerm_substitute (requestSize vertex rely target focus kind sort)]
  change (normalizedOutput vertex rely target focus kind sort).substitute
    (liftSubstitution (liftSubstitution (parameterMapping rely target focus kind sort))) = _
  rw [normalizedOutput_eq]
  let mapping : Substitution (symbols D) 2 2 := parameterMapping rely target focus kind sort
  change (originalSecond rely target kind sort).substitute (liftSubstitution (liftSubstitution mapping)) = _
  simp only [originalSecond, originalFirst, applyVariableTerm_substitute,
    originalMembership, typingType_substitute, IndexSyntax.classifierValue_substitute,
    TermExpr.substitute, liftSubstitution_zero, codeType_substitute,
    certifiedCode_substitute, TypeExpr.substitute]
  have mappingEq : mapping = Fin.cases (constantContinuation rely target kind sort)
      (fun _ => (.var 1 : TermExpr (symbols D) 2)) := by
    funext position
    cases position using Fin.cases with
    | zero => rfl
    | succ position =>
        have zero : position = 0 := Fin.eq_zero position
        cases zero
        rfl
  rw [mappingEq]
  simp only [secondApplication, firstApplication, membershipType, relyTerm,
    classifierValue_rename]
  rfl

private def restoreSubstitution {n m k : Nat} (same : n = m)
    (source : ContextExpr (symbols D) k) (destination : ContextExpr (symbols D) n)
    (mapping : Substitution (symbols D) m k)
    (typed : Derivation (Theory vertex) (.substitution source (resizeContext same destination) mapping)) :
    Derivation (Theory vertex) (.substitution source destination
      (fun position => mapping (Fin.cast same position))) := by
  cases same
  exact typed

theorem parameterClassifierTerm_single :
    SingleRelyEvidence.parameterClassifierTerm (D := D) (interface rely target focus kind sort) 0 =
      classifierValue rely kind (.var (1 : Fin 2)) := by
  unfold SingleRelyEvidence.parameterClassifierTerm
  rw [ContinuationSemantics.relyEntry]
  simp only [IndexSyntax.classifierValue_substitute, TermExpr.substitute]
  change classifierValue rely kind (.var (1 : Fin 2)) = _
  rfl

def requestTyped : Derivation (Theory vertex)
    (.substitution (withEvidence rely target kind sort)
      (generatedSyntax vertex rely target focus kind sort).scope
      (requestMapping vertex rely target focus kind sort)) := by
  let mapping : Substitution (symbols D) 2 2 := parameterMapping rely target focus kind sort
  let first := deriveList (.substitutionLift (pairContext rely target kind sort)
    (parameters (D := D) (interface rely target focus kind sort)) (codeType rely 2)
    mapping)
    (.cons (parametersTyped vertex rely target focus kind sort)
      (.cons (codeFormed vertex rely (parametersFormed vertex (interface rely target focus kind sort))) .nil))
  have firstTyped : Derivation (Theory vertex)
      (.substitution (withValue rely target kind sort)
        (.snoc (parameters (D := D) (interface rely target focus kind sort)) (codeType rely 2))
        (liftSubstitution mapping)) := by
    change Derivation (Theory vertex)
      (.substitution ((pairContext rely target kind sort).snoc ((codeType rely 2).substitute mapping))
        (.snoc (parameters (D := D) (interface rely target focus kind sort)) (codeType rely 2))
        (liftSubstitution mapping)) at first
    rw [codeType_substitute rely mapping] at first
    exact first
  have memberFormed : Derivation (Theory vertex)
      (.type (.snoc (parameters (D := D) (interface rely target focus kind sort)) (codeType rely 2))
        (originalMembership rely kind)) := by
    have classifier := SingleRelyEvidence.parameterClassifierTyped vertex
      (interface rely target focus kind sort) 0
    rw [parameterClassifierTerm_single] at classifier
    have namedClassifier : Derivation (Theory vertex)
        (.term (parameters (D := D) (interface rely target focus kind sort))
          (classifierValue rely kind (.var (1 : Fin 2))) (codeType rely 2)) := classifier
    have there := weakenTerm vertex namedClassifier
      (codeFormed vertex rely (parametersFormed vertex (interface rely target focus kind sort)))
    rw [codeType_rename rely (Fin.succ : Renaming 2 3)] at there
    exact typingFormed vertex rely
      (extendFormed vertex (parametersFormed vertex (interface rely target focus kind sort))
        (codeFormed vertex rely (parametersFormed vertex (interface rely target focus kind sort))))
      (.var 0) (classifierValue rely kind (.var 2))
      (codeVariable vertex rely (parametersFormed vertex (interface rely target focus kind sort)))
      (by
        rw [classifierValue_rename rely kind (.var (1 : Fin 2)) (Fin.succ : Renaming 2 3)] at there
        exact there)
  have transported : (originalMembership (D := D) rely kind).substitute
      (liftSubstitution mapping) = membershipType rely kind := by
    change (originalMembership (D := D) rely kind).substitute
      (liftSubstitution (parameterMapping rely target focus kind sort : Substitution (symbols D) 2 2)) = _
    rw [parameterMapping_explicit]
    simp only [originalMembership, typingType_substitute, IndexSyntax.classifierValue_substitute,
      TermExpr.substitute, membershipType, relyTerm, classifierValue_rename]
    rfl
  have second := deriveList (.substitutionLift (withValue rely target kind sort)
    (.snoc (parameters (D := D) (interface rely target focus kind sort)) (codeType rely 2))
    (originalMembership rely kind) (liftSubstitution mapping))
    (.cons firstTyped (.cons memberFormed .nil))
  have normalized : Derivation (Theory vertex)
      (.substitution (withEvidence rely target kind sort)
        (normalizedContext vertex rely target focus kind sort)
        (liftSubstitution (liftSubstitution mapping))) := by
    rw [normalizedContext_eq]
    simpa only [RuleCode.conclusion, transported] using second
  exact restoreSubstitution vertex (requestSize vertex rely target focus kind sort)
    (withEvidence rely target kind sort) (generatedSyntax vertex rely target focus kind sort).scope
    (liftSubstitution (liftSubstitution mapping)) normalized

/-- The applied output retains its actual generated target annotation. -/
def generated_target_beta : Derivation (Theory vertex)
    (.termEq (withEvidence rely target kind sort)
      ((generatedSyntax vertex rely target focus kind sort).output.substitute
        (requestMapping vertex rely target focus kind sort)) (.var 2) (certifiedCode target sort 4)) := by
  rw [output_substitute]
  exact target_beta vertex rely target kind sort

theorem rely_substitute :
    (ContinuationSemantics.relyValueTerm vertex (interface rely target focus kind sort) 0).substitute
      (requestMapping vertex rely target focus kind sort) = (.var 1 : TermExpr (symbols D) 4) := by
  change (ContinuationSemantics.relyValueTerm vertex (interface rely target focus kind sort) 0).substitute
    (fun position => (liftSubstitution (liftSubstitution (parameterMapping rely target focus kind sort)))
      (Fin.cast (requestSize vertex rely target focus kind sort) position)) = _
  rw [← resizeTerm_substitute (requestSize vertex rely target focus kind sort), normalizedRely_eq]
  rfl

end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.SingleRelyBeta
