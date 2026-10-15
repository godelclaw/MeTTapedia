import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeMonotoneFormation

/-!
# Finite evidence for native monotone operators

The witnesses below are ordinary trees of the generated native rules. Their
certificates are checked against the complete higher-order monotonicity
proposition, rather than an external variance or semantic oracle.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeMonotoneCertificateControls

open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open Mettapedia.OSLF.NativeTypes.Generation
open FixedPointSyntax NativeMonotoneSyntax NativeMonotoneFormation

universe u
variable {S : Symbols.{u}} {D : Signature S} {n : Nat}

def identityOperator (domain : TypeExpr S n) : TermExpr S n :=
  .lam (predicateType domain) ((predicateType domain).rename Fin.succ) (.var 0)


def identityTyping (context : ContextExpr S n) (domain : TypeExpr S n)
    (formed : Derivation D (.context context))
    (domainFormed : Derivation D (.type context domain)) :
    Derivation D (.term context (identityOperator domain) (operatorType domain)) := by
  let predicates := NativeEquality.predicateFormation context domain formed domainFormed
  let extended := extendContext context (predicateType domain) formed predicates
  have variableTyped : Derivation D (.term (.snoc context (predicateType domain)) (.var 0)
      ((predicateType domain).rename Fin.succ)) := by
    simpa only [RuleCode.conclusion, ContextExpr.lookup_zero] using
      deriveList (.variable (.snoc context (predicateType domain)) 0) (.cons extended .nil)
  exact deriveList (.lambda context (predicateType domain)
    ((predicateType domain).rename Fin.succ) (.var 0))
    (.cons predicates (.cons
      (NativeEquality.weakenType context (predicateType domain) (predicateType domain)
        predicates predicates) (.cons variableTyped .nil)))




def identityApplication (context : ContextExpr S n) (domain : TypeExpr S n)
    (candidate : TermExpr S n) (formed : Derivation D (.context context))
    (domainFormed : Derivation D (.type context domain))
    (candidateTyped : Derivation D (.term context candidate (predicateType domain))) :
    Derivation D (.termEq context (applyOperator domain (identityOperator domain) candidate)
      candidate (predicateType domain)) := by
  let predicates := NativeEquality.predicateFormation context domain formed domainFormed
  let extended := extendContext context (predicateType domain) formed predicates
  have variableTyped : Derivation D (.term (.snoc context (predicateType domain)) (.var 0)
      ((predicateType domain).rename Fin.succ)) := by
    simpa only [RuleCode.conclusion, ContextExpr.lookup_zero] using
      deriveList (.variable (.snoc context (predicateType domain)) 0) (.cons extended .nil)
  have original := deriveList (.piBeta context (predicateType domain)
      ((predicateType domain).rename Fin.succ) (.var 0) candidate)
      (.cons predicates (.cons
        (NativeEquality.weakenType context (predicateType domain) (predicateType domain)
          predicates predicates) (.cons variableTyped (.cons candidateTyped .nil))))
  change Derivation D (.termEq context (applyOperator domain (identityOperator domain) candidate)
    candidate (((predicateType domain).rename Fin.succ).substitute (instantiate candidate))) at original
  rw [TypeExpr.instantiate_weaken] at original
  exact original



theorem identityOperator_rename {m : Nat} (mapping : Renaming n m) (domain : TypeExpr S n) :
    (identityOperator domain).rename mapping = identityOperator (domain.rename mapping) := by
  simp only [identityOperator, predicateType, TermExpr.rename, TypeExpr.rename, liftRenaming_zero]
  congr 2
  rw [TypeExpr.rename_comp, TypeExpr.rename_comp]
  rfl

def identityMonotonicityAt (context : ContextExpr S n) (domain : TypeExpr S n)
    (first second : TermExpr S n) (formed : Derivation D (.context context))
    (domainFormed : Derivation D (.type context domain))
    (firstTyped : Derivation D (.term context first (predicateType domain)))
    (secondTyped : Derivation D (.term context second (predicateType domain))) :
    Derivation D (.entails context (monotonicityAt domain (identityOperator domain) first second)) := by
  let before := inclusion domain first second
  let after := inclusion domain (applyOperator domain (identityOperator domain) first)
    (applyOperator domain (identityOperator domain) second)
  let beforeFormed := inclusionFormation context domain first second formed domainFormed firstTyped secondTyped
  let operatorTyped := identityTyping context domain formed domainFormed
  let afterFormed := inclusionFormation context domain _ _ formed domainFormed
    (operatorApplicationTyping context domain _ _ formed domainFormed operatorTyped firstTyped)
    (operatorApplicationTyping context domain _ _ formed domainFormed operatorTyped secondTyped)
  let converted := inclusionCongruence context domain _ first _ second formed domainFormed
    (identityApplication context domain first formed domainFormed firstTyped)
    (identityApplication context domain second formed domainFormed secondTyped) firstTyped secondTyped
  let weakening := deriveList (.substitutionWeakenAssumption context before) (.cons beforeFormed .nil)
  have afterToBefore : Derivation D (.predicateEq (.assume context before) after before) := by
    simpa only [RuleCode.conclusion, PropExpr.substitute_identity] using
      deriveList (.substitutePredicateEquality (.assume context before) context TermExpr.var after before)
        (.cons weakening (.cons converted .nil))
  have beforeInAssumption : Derivation D (.predicate (.assume context before) before) := by
    simpa only [RuleCode.conclusion, PropExpr.substitute_identity] using
      deriveList (.substitutePredicate (.assume context before) context TermExpr.var before)
        (.cons weakening (.cons beforeFormed .nil))
  let assumptionContext := deriveList (.contextAssume context before)
    (.cons formed (.cons beforeFormed .nil))
  let hypothesis := deriveList (.hypothesis (.assume context before) before (.here context before))
    (.cons assumptionContext (.cons beforeInAssumption .nil))
  let consequent := deriveList (.entailmentConversion (.assume context before) before after)
    (.cons (deriveList (.predicateSymmetry (.assume context before) after before)
      (.cons afterToBefore .nil)) (.cons hypothesis .nil))
  exact deriveList (.implicationIntroduction context before after)
    (.cons beforeFormed (.cons afterFormed (.cons consequent .nil)))

def identityMonotonicity (context : ContextExpr S n) (domain : TypeExpr S n)
    (formed : Derivation D (.context context))
    (domainFormed : Derivation D (.type context domain)) :
    Derivation D (.entails context (monotonicity domain (identityOperator domain))) := by
  let predicates := NativeEquality.predicateFormation context domain formed domainFormed
  let firstContext := extendContext context (predicateType domain) formed predicates
  let firstDomain := NativeEquality.weakenType context (predicateType domain) domain predicates domainFormed
  let firstPredicates := NativeEquality.predicateFormation _ _ firstContext firstDomain
  let secondContext := extendContext _ _ firstContext firstPredicates
  let secondDomain := NativeEquality.weakenType _ _ _ firstPredicates firstDomain
  have firstTyped : Derivation D (.term
      ((context.snoc (predicateType domain)).snoc (predicateType (domain.rename Fin.succ))) (.var 1)
      (predicateType (domain.rename Fin.succ |>.rename Fin.succ))) := by
    have original : Derivation D (.term
        ((context.snoc (predicateType domain)).snoc (predicateType (domain.rename Fin.succ)))
        (.var (Fin.succ (0 : Fin (n + 1))))
        (predicateType (domain.rename Fin.succ |>.rename Fin.succ))) := by
      simpa only [RuleCode.conclusion, ContextExpr.lookup_succ, ContextExpr.lookup_zero,
        predicateType, NativeEquality.predicateType, TypeExpr.rename] using
        deriveList (.variable _ (Fin.succ (0 : Fin (n + 1)))) (.cons secondContext .nil)
    have index : Fin.succ (0 : Fin (n + 1)) = (1 : Fin (n + 1 + 1)) := by
      apply Fin.ext
      simp
    simpa only [index] using original
  have secondTyped : Derivation D (.term
      ((context.snoc (predicateType domain)).snoc (predicateType (domain.rename Fin.succ))) (.var 0)
      (predicateType (domain.rename Fin.succ |>.rename Fin.succ))) := by
    simpa only [RuleCode.conclusion, ContextExpr.lookup_zero, predicateType, NativeEquality.predicateType, TypeExpr.rename] using
      deriveList (.variable _ 0) (.cons secondContext .nil)
  let matrix := identityMonotonicityAt _ _ (.var 1) (.var 0)
    secondContext secondDomain firstTyped secondTyped
  let operatorTyped := identityTyping _ _ secondContext secondDomain
  let antecedent := inclusionFormation _ _ (.var 1) (.var 0)
    secondContext secondDomain firstTyped secondTyped
  let consequent := inclusionFormation _ _ _ _ secondContext secondDomain
    (operatorApplicationTyping _ _ _ _ secondContext secondDomain operatorTyped firstTyped)
    (operatorApplicationTyping _ _ _ _ secondContext secondDomain operatorTyped secondTyped)
  let matrixFormed := deriveList (.implicationFormation _ _ _)
    (.cons antecedent (.cons consequent .nil))
  let inner := deriveList (.universalIntroduction _ _ _)
    (.cons firstPredicates (.cons matrixFormed (.cons matrix .nil)))
  let innerFormed := deriveList (.universalFormation _ _ _)
    (.cons firstPredicates (.cons matrixFormed .nil))
  simpa only [RuleCode.conclusion, monotonicity, monotonicityUnderPredicate,
    identityOperator_rename, monotonicityAt, NativeEquality.predicateType, predicateType] using
    deriveList (.universalIntroduction context (predicateType domain) _)
      (.cons predicates (.cons innerFormed (.cons inner .nil)))

def constantOperator (domain : TypeExpr S n) (value : TermExpr S n) : TermExpr S n :=
  .lam (predicateType domain) ((predicateType domain).rename Fin.succ) (value.rename Fin.succ)

def constantTyping (context : ContextExpr S n) (domain : TypeExpr S n) (value : TermExpr S n)
    (formed : Derivation D (.context context))
    (domainFormed : Derivation D (.type context domain))
    (valueTyped : Derivation D (.term context value (predicateType domain))) :
    Derivation D (.term context (constantOperator domain value) (operatorType domain)) := by
  let predicates := NativeEquality.predicateFormation context domain formed domainFormed
  exact deriveList (.lambda context (predicateType domain) ((predicateType domain).rename Fin.succ)
    (value.rename Fin.succ))
    (.cons predicates (.cons
      (NativeEquality.weakenType context (predicateType domain) (predicateType domain) predicates predicates)
      (.cons (NativeEquality.weakenTerm context (predicateType domain) (predicateType domain)
        value predicates valueTyped) .nil)))

def constantApplication (context : ContextExpr S n) (domain : TypeExpr S n)
    (value candidate : TermExpr S n) (formed : Derivation D (.context context))
    (domainFormed : Derivation D (.type context domain))
    (valueTyped : Derivation D (.term context value (predicateType domain)))
    (candidateTyped : Derivation D (.term context candidate (predicateType domain))) :
    Derivation D (.termEq context (applyOperator domain (constantOperator domain value) candidate)
      value (predicateType domain)) := by
  let predicates := NativeEquality.predicateFormation context domain formed domainFormed
  have original := deriveList (.piBeta context (predicateType domain)
    ((predicateType domain).rename Fin.succ) (value.rename Fin.succ) candidate)
    (.cons predicates (.cons
      (NativeEquality.weakenType context (predicateType domain) (predicateType domain) predicates predicates)
      (.cons (NativeEquality.weakenTerm context (predicateType domain) (predicateType domain)
        value predicates valueTyped) (.cons candidateTyped .nil))))
  change Derivation D (.termEq context (applyOperator domain (constantOperator domain value) candidate)
    ((value.rename Fin.succ).substitute (instantiate candidate))
    (((predicateType domain).rename Fin.succ).substitute (instantiate candidate))) at original
  rw [TypeExpr.instantiate_weaken, TermExpr.instantiate_weaken] at original
  exact original

theorem constantOperator_rename {m : Nat} (mapping : Renaming n m)
    (domain : TypeExpr S n) (value : TermExpr S n) :
    (constantOperator domain value).rename mapping =
      constantOperator (domain.rename mapping) (value.rename mapping) := by
  simp only [constantOperator, TermExpr.rename]
  have bodyType : ((predicateType domain).rename Fin.succ).rename (liftRenaming mapping) =
      (predicateType (domain.rename mapping)).rename Fin.succ := by
    change ((predicateType domain).rename Fin.succ).rename (liftRenaming mapping) =
      ((predicateType domain).rename mapping).rename Fin.succ
    rw [TypeExpr.rename_comp, TypeExpr.rename_comp]
    rfl
  have bodyTerm : (value.rename Fin.succ).rename (liftRenaming mapping) =
      (value.rename mapping).rename Fin.succ := by
    rw [TermExpr.rename_comp, TermExpr.rename_comp]
    rfl
  rw [bodyType, bodyTerm]
  rfl

def inclusionReflexivity (context : ContextExpr S n) (domain : TypeExpr S n)
    (value : TermExpr S n) (formed : Derivation D (.context context))
    (domainFormed : Derivation D (.type context domain))
    (valueTyped : Derivation D (.term context value (predicateType domain))) :
    Derivation D (.entails context (inclusion domain value value)) := by
  let extended := extendContext context domain formed domainFormed
  let weakenedDomain := NativeEquality.weakenType context domain domain domainFormed domainFormed
  have variableTyped : Derivation D (.term (.snoc context domain) (.var 0) (domain.rename Fin.succ)) := by
    simpa only [RuleCode.conclusion, ContextExpr.lookup_zero] using
      deriveList (.variable (.snoc context domain) 0) (.cons extended .nil)
  have weakenedValue : Derivation D (.term (.snoc context domain) (value.rename Fin.succ)
      (predicateType (domain.rename Fin.succ))) := by
    simpa only [predicateType, NativeEquality.predicateType, TypeExpr.rename] using
      NativeEquality.weakenTerm context domain (predicateType domain) value domainFormed valueTyped
  let body := application (domain.rename Fin.succ) (value.rename Fin.succ) (.var 0)
  let bodyFormed := applicationFormation _ _ _ _ extended weakenedDomain weakenedValue variableTyped
  let assumptionContext := deriveList (.contextAssume _ body) (.cons extended (.cons bodyFormed .nil))
  let weakening := deriveList (.substitutionWeakenAssumption _ body) (.cons bodyFormed .nil)
  have assumedBody : Derivation D (.predicate (.assume (.snoc context domain) body) body) := by
    simpa only [RuleCode.conclusion, PropExpr.substitute_identity] using
      deriveList (.substitutePredicate (.assume (.snoc context domain) body) (.snoc context domain)
        TermExpr.var body) (.cons weakening (.cons bodyFormed .nil))
  let hypothesis := deriveList (.hypothesis _ body (.here _ body))
    (.cons assumptionContext (.cons assumedBody .nil))
  let implication := deriveList (.implicationIntroduction _ body body)
    (.cons bodyFormed (.cons bodyFormed (.cons hypothesis .nil)))
  exact deriveList (.universalIntroduction context domain _)
    (.cons domainFormed (.cons (deriveList (.implicationFormation _ body body)
      (.cons bodyFormed (.cons bodyFormed .nil))) (.cons implication .nil)))

def constantMonotonicityAt (context : ContextExpr S n) (domain : TypeExpr S n)
    (value first second : TermExpr S n) (formed : Derivation D (.context context))
    (domainFormed : Derivation D (.type context domain))
    (valueTyped : Derivation D (.term context value (predicateType domain)))
    (firstTyped : Derivation D (.term context first (predicateType domain)))
    (secondTyped : Derivation D (.term context second (predicateType domain))) :
    Derivation D (.entails context (monotonicityAt domain (constantOperator domain value) first second)) := by
  let before := inclusion domain first second
  let after := inclusion domain (applyOperator domain (constantOperator domain value) first)
    (applyOperator domain (constantOperator domain value) second)
  let self := inclusion domain value value
  let beforeFormed := inclusionFormation context domain first second formed domainFormed firstTyped secondTyped
  let operatorTyped := constantTyping context domain value formed domainFormed valueTyped
  let afterFormed := inclusionFormation context domain _ _ formed domainFormed
    (operatorApplicationTyping context domain _ _ formed domainFormed operatorTyped firstTyped)
    (operatorApplicationTyping context domain _ _ formed domainFormed operatorTyped secondTyped)
  let converted := inclusionCongruence context domain _ value _ value formed domainFormed
    (constantApplication context domain value first formed domainFormed valueTyped firstTyped)
    (constantApplication context domain value second formed domainFormed valueTyped secondTyped)
    valueTyped valueTyped
  let weakening := deriveList (.substitutionWeakenAssumption context before) (.cons beforeFormed .nil)
  have afterToSelf : Derivation D (.predicateEq (.assume context before) after self) := by
    simpa only [RuleCode.conclusion, PropExpr.substitute_identity] using
      deriveList (.substitutePredicateEquality (.assume context before) context TermExpr.var after self)
        (.cons weakening (.cons converted .nil))
  have selfTrue : Derivation D (.entails (.assume context before) self) := by
    simpa only [RuleCode.conclusion, PropExpr.substitute_identity] using
      deriveList (.substituteEntailment (.assume context before) context TermExpr.var self)
        (.cons weakening (.cons (inclusionReflexivity context domain value formed domainFormed valueTyped) .nil))
  let consequent := deriveList (.entailmentConversion (.assume context before) self after)
    (.cons (deriveList (.predicateSymmetry (.assume context before) after self)
      (.cons afterToSelf .nil)) (.cons selfTrue .nil))
  exact deriveList (.implicationIntroduction context before after)
    (.cons beforeFormed (.cons afterFormed (.cons consequent .nil)))

def constantMonotonicity (context : ContextExpr S n) (domain : TypeExpr S n)
    (value : TermExpr S n) (formed : Derivation D (.context context))
    (domainFormed : Derivation D (.type context domain))
    (valueTyped : Derivation D (.term context value (predicateType domain))) :
    Derivation D (.entails context (monotonicity domain (constantOperator domain value))) := by
  let predicates := NativeEquality.predicateFormation context domain formed domainFormed
  let firstContext := extendContext context (predicateType domain) formed predicates
  let firstDomain := NativeEquality.weakenType context (predicateType domain) domain predicates domainFormed
  let firstPredicates := NativeEquality.predicateFormation _ _ firstContext firstDomain
  let secondContext := extendContext _ _ firstContext firstPredicates
  let secondDomain := NativeEquality.weakenType _ _ _ firstPredicates firstDomain
  have firstTyped : Derivation D (.term
      ((context.snoc (predicateType domain)).snoc (predicateType (domain.rename Fin.succ))) (.var 1)
      (predicateType (domain.rename Fin.succ |>.rename Fin.succ))) := by
    have original : Derivation D (.term
        ((context.snoc (predicateType domain)).snoc (predicateType (domain.rename Fin.succ)))
        (.var (Fin.succ (0 : Fin (n + 1))))
        (predicateType (domain.rename Fin.succ |>.rename Fin.succ))) := by
      simpa only [RuleCode.conclusion, ContextExpr.lookup_succ, ContextExpr.lookup_zero,
        predicateType, NativeEquality.predicateType, TypeExpr.rename] using
        deriveList (.variable _ (Fin.succ (0 : Fin (n + 1)))) (.cons secondContext .nil)
    have index : Fin.succ (0 : Fin (n + 1)) = (1 : Fin (n + 1 + 1)) := by
      apply Fin.ext
      simp
    simpa only [index] using original
  have secondTyped : Derivation D (.term
      ((context.snoc (predicateType domain)).snoc (predicateType (domain.rename Fin.succ))) (.var 0)
      (predicateType (domain.rename Fin.succ |>.rename Fin.succ))) := by
    simpa only [RuleCode.conclusion, ContextExpr.lookup_zero,
      predicateType, NativeEquality.predicateType, TypeExpr.rename] using
      deriveList (.variable _ 0) (.cons secondContext .nil)
  have firstValue : Derivation D (.term (context.snoc (predicateType domain)) (value.rename Fin.succ)
      (predicateType (domain.rename Fin.succ))) := by
    simpa only [predicateType, NativeEquality.predicateType, TypeExpr.rename] using
      NativeEquality.weakenTerm context (predicateType domain) (predicateType domain) value predicates valueTyped
  have secondValue : Derivation D (.term
      ((context.snoc (predicateType domain)).snoc (predicateType (domain.rename Fin.succ)))
      (value.rename Fin.succ |>.rename Fin.succ)
      (predicateType (domain.rename Fin.succ |>.rename Fin.succ))) := by
    simpa only [predicateType, NativeEquality.predicateType, TypeExpr.rename] using
      NativeEquality.weakenTerm _ _ _ _ firstPredicates firstValue
  let matrix := constantMonotonicityAt _ _ _ (.var 1) (.var 0)
    secondContext secondDomain secondValue firstTyped secondTyped
  let operatorTyped := constantTyping _ _ _ secondContext secondDomain secondValue
  let antecedent := inclusionFormation _ _ (.var 1) (.var 0)
    secondContext secondDomain firstTyped secondTyped
  let consequent := inclusionFormation _ _ _ _ secondContext secondDomain
    (operatorApplicationTyping _ _ _ _ secondContext secondDomain operatorTyped firstTyped)
    (operatorApplicationTyping _ _ _ _ secondContext secondDomain operatorTyped secondTyped)
  let matrixFormed := deriveList (.implicationFormation _ _ _)
    (.cons antecedent (.cons consequent .nil))
  let inner := deriveList (.universalIntroduction _ _ _)
    (.cons firstPredicates (.cons matrixFormed (.cons matrix .nil)))
  let innerFormed := deriveList (.universalFormation _ _ _)
    (.cons firstPredicates (.cons matrixFormed .nil))
  simpa only [RuleCode.conclusion, monotonicity, monotonicityUnderPredicate,
    constantOperator_rename, monotonicityAt, NativeEquality.predicateType, predicateType] using
    deriveList (.universalIntroduction context (predicateType domain) _)
      (.cons predicates (.cons innerFormed (.cons inner .nil)))

def truthPredicate (domain : TypeExpr S n) : TermExpr S n :=
  .lam domain .propositions (.quote .truth)

def truthPredicateTyping (context : ContextExpr S n) (domain : TypeExpr S n)
    (formed : Derivation D (.context context))
    (domainFormed : Derivation D (.type context domain)) :
    Derivation D (.term context (truthPredicate domain) (predicateType domain)) := by
  let extended := extendContext context domain formed domainFormed
  exact deriveList (.lambda context domain .propositions (.quote .truth))
    (.cons domainFormed (.cons (deriveList (.propositionType _) (.cons extended .nil))
      (.cons (deriveList (.quote _ .truth)
        (.cons (deriveList (.truthFormation _) (.cons extended .nil)) .nil)) .nil)))

variable [DecidableEq S.TypeSymbol] [DecidableEq S.TermSymbol] [DecidableEq S.PredicateSymbol]

theorem identity_checked (context : ContextExpr S n) (domain : TypeExpr S n)
    (tested : TermExpr S n) (formed : Derivation D (.context context))
    (domainFormed : Derivation D (.type context domain))
    (testedTyped : Derivation D (.term context tested domain)) :
    NativeMonotoneSyntax.check D context domain (identityOperator domain) tested
      (Certificates.Refinement.erase (identityTyping context domain formed domainFormed))
      (Certificates.Refinement.erase (identityMonotonicity context domain formed domainFormed))
      (Certificates.Refinement.erase testedTyped) = true := by
  apply (NativeMonotoneSyntax.check_exact D _ _ _ _ _ _ _).mpr
  exact ⟨Certificates.Refinement.check_erase _, Certificates.Refinement.check_erase _,
    Certificates.Refinement.check_erase _⟩

theorem constant_checked (context : ContextExpr S n) (domain : TypeExpr S n)
    (value tested : TermExpr S n) (formed : Derivation D (.context context))
    (domainFormed : Derivation D (.type context domain))
    (valueTyped : Derivation D (.term context value (predicateType domain)))
    (testedTyped : Derivation D (.term context tested domain)) :
    NativeMonotoneSyntax.check D context domain (constantOperator domain value) tested
      (Certificates.Refinement.erase (constantTyping context domain value formed domainFormed valueTyped))
      (Certificates.Refinement.erase (constantMonotonicity context domain value formed domainFormed valueTyped))
      (Certificates.Refinement.erase testedTyped) = true := by
  apply (NativeMonotoneSyntax.check_exact D _ _ _ _ _ _ _).mpr
  exact ⟨Certificates.Refinement.check_erase _, Certificates.Refinement.check_erase _,
    Certificates.Refinement.check_erase _⟩

theorem constantTruth_generated (context : ContextExpr S n) (domain : TypeExpr S n)
    (tested : TermExpr S n) (formed : Derivation D (.context context))
    (domainFormed : Derivation D (.type context domain))
    (testedTyped : Derivation D (.term context tested domain)) :
    NativeMonotoneSyntax.generate D context domain
      (constantOperator domain (truthPredicate domain)) tested
      (Certificates.Refinement.erase (constantTyping context domain (truthPredicate domain)
        formed domainFormed (truthPredicateTyping context domain formed domainFormed)))
      (Certificates.Refinement.erase (constantMonotonicity context domain (truthPredicate domain)
        formed domainFormed (truthPredicateTyping context domain formed domainFormed)))
      (Certificates.Refinement.erase testedTyped) =
      some (NativeMonotoneSyntax.least domain (constantOperator domain (truthPredicate domain)) tested,
        NativeMonotoneSyntax.greatest domain (constantOperator domain (truthPredicate domain)) tested) :=
  NativeMonotoneSyntax.generate_of_checked D context domain _ tested _ _ _
    (constant_checked context domain (truthPredicate domain) tested formed domainFormed
      (truthPredicateTyping context domain formed domainFormed) testedTyped)

def wrongMonotonicity (context : ContextExpr S n)
    (formed : Derivation D (.context context)) : Certificates.Refinement.Certificate D :=
  .node (.truthIntroduction context) (fun _ => Certificates.Refinement.erase formed)

theorem wrongMonotonicity_rejected (context : ContextExpr S n) (domain : TypeExpr S n)
    (operator : TermExpr S n) (formed : Derivation D (.context context)) :
    Certificates.Refinement.check (wrongMonotonicity context formed)
      (.entails context (monotonicity domain operator)) = false := by
  have different : RuleCode.conclusion (D := D) (.truthIntroduction context) ≠
      .entails context (monotonicity domain operator) := by
    intro same
    cases same
  simp only [Certificates.Refinement.check, wrongMonotonicity, Certificates.Tree.check,
    Certificates.Refinement.presentation, different, decide_false, Bool.false_and]

theorem wrongMonotonicity_generates_none (context : ContextExpr S n) (domain : TypeExpr S n)
    (operator tested : TermExpr S n) (formed : Derivation D (.context context))
    (operatorCertificate argumentCertificate : Certificates.Refinement.Certificate D) :
    NativeMonotoneSyntax.generate D context domain operator tested operatorCertificate
      (wrongMonotonicity context formed) argumentCertificate = none := by
  simp only [NativeMonotoneSyntax.generate, NativeMonotoneSyntax.check,
    wrongMonotonicity_rejected, Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]

end Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeMonotoneCertificateControls
