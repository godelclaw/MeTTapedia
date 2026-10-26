import Mettapedia.Languages.MM0.HOLKernelSetOperationContextReadback
import Mettapedia.Languages.MM0.HOLKernelStructuralReadback

/-!
# Admission of the maintained HOL logical and equality rule instances

All twenty-one inference schemas read their actual native premises and
conclusion to the typed source operands' ordered sequent. The operands can
use any native representations successfully decoded by the structural term
reader. Canonical argument lists instantiate this shared result. This includes discharged object typings,
the Boolean-equivalence abbreviation and both application congruence rules.

A licensed, checked native application with independently admitted children
therefore constructs an admitted parent tree. The proofs cover arbitrary
intrinsic frames within the explicit name-bank bounds. They supply local
compiler closure; assembling every complete compiler output still requires
its environment, binding and conversion invariants.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.MM0.HOLKernelInferenceReadback
open Mettapedia.Logic.HOL
open Kernel HOLKernelSyntax HOLKernelTermReadback HOLKernelJudgmentReadback
open HOLKernelRuleReadback HOLKernelRuleInstances
open HOLKernelSetOperationProofReadback
open Embedding.ZFSetHenkinInterpretation (Symbol)
variable {gamma : Ctx Unit}

section OperandReadback
universe u
variable {Const : Ty Unit → Type u}
variable {terms : TermSignature} {definitions : Definition.Signature}
variable {references : HOLKernelSyntax.Symbol → Nat} {ids : SortIds}

set_option maxHeartbeats 1000000 in
/-- The exact native instantiation of every nonbinding HOL inference schema
reads to its typed source premises and conclusion. Operands may use arbitrary
native representations accepted by the term reader. -/
theorem read_instance_of_operands {context : Context}
    (faithful : Function.Injective references)
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions references ids)
    (distinct : ∀ symbol, references symbol ≠ abbreviation.reference)
    (extras : {gamma : Ctx Unit} → Preterm → Option (Decoded Const gamma))
    (constants : Nat → Option (NamedElaboration.SomeConst Const)) (parameters : Nat)
    (names : Names gamma) (rule : HOLKernelInferenceRules.Rule)
    (nativeArguments : List Preterm) (arguments : InferenceArguments Const gamma rule)
    (parsed : readInferenceArguments (readTermWith extras references constants parameters)
      references names rule (nativeArguments.map (expandEquivalence references abbreviation.reference)) = some arguments)
    (nativeInstance : TheoremInstance)
    (instantiated : TheoremDecl.Instantiates terms context
      (rule.declaration references ids abbreviation.reference) nativeArguments nativeInstance) :
    nativeInstance.hypotheses.mapM
      (readFormulaIn abbreviation (readTermWith extras references constants parameters) parameters names) =
      some arguments.premises ∧
    readFormulaIn abbreviation (readTermWith extras references constants parameters) parameters names
      nativeInstance.conclusion = some arguments.conclusion := by
  have hypotheses := (Substitution.substituteList_eq_some_iff _ _ _).mpr instantiated.hypotheses
  have conclusion := instantiated.conclusion.eval
  rcases nativeArguments with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, _ | ⟨g, rest⟩⟩⟩⟩⟩⟩⟩ <;>
    cases rule <;> simp only [List.map_cons, List.map_nil, readInferenceArguments] at parsed <;>
    try contradiction
  all_goals
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
      readObjectWith] at parsed
  all_goals
    obtain ⟨antecedent, antecedentRead, parsed⟩ := parsed
    obtain ⟨contextJudgment, contextParsed, rfl⟩ := Option.map_eq_some_iff.mp antecedentRead
  all_goals try (split at parsed <;> try contradiction)
  all_goals
    try simp only [Option.bind_eq_some_iff, Option.some.injEq,
      expect_eq_some_iff, exists_eq_right] at parsed
  all_goals repeat' obtain ⟨value, valueRead, parsed⟩ := parsed
  all_goals
    simp [HOLKernelInferenceRules.Rule.declaration,
      HOLKernelJudgment.entails, HOLKernelJudgment.holds, HOLKernelJudgment.conjunction,
      HOLKernelJudgment.hasType, HOLKernelTypingRules.typed, HOLKernelTypingRules.boolType,
      HOLKernelTypingRules.functionType, HOLKernelInferenceRules.equality,
      HOLKernelInferenceRules.equivalence, applySymbol, Preterm.applyArgs,
      Preterm.substitute, Substitution.ofList, Substitution.substituteList] at hypotheses conclusion
  all_goals
    first | rw [← hypotheses] | rw [hypotheses]
    rw [← conclusion]
    clear instantiated hypotheses conclusion
    simp_all [readFormulaIn, expandEquivalence,
      HOLKernelBooleanEquality.expanded, applySymbol, Preterm.applyArgs,
      readJudgmentWith, readHead_reference references faithful,
      readTermWith, readTypingWith, readType, logicalBinary, expect_same,
      Judgment.formula, InferenceArguments.premises, InferenceArguments.conclusion]
  all_goals
    unfold readTermWith
    simp_all [readHead_reference references faithful, readTermWith, application, expect_same, Judgment.formula]

/-- Actual theorem-table authority and operand reading construct independent
local admission, without a canonical encoding or a source proof input. -/
def admittedApplicationOfOperands {context : Context} {theorems : TheoremSignature}
    (faithful : Function.Injective references)
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions references ids)
    (distinct : ∀ symbol, references symbol ≠ abbreviation.reference)
    (extras : {gamma : Ctx Unit} → Preterm → Option (Decoded Const gamma))
    (constants : Nat → Option (NamedElaboration.SomeConst Const)) (parameters : Nat)
    (rules : HOLKernelInferenceRules.Rules theorems references ids abbreviation.reference)
    (names : Names gamma) (rule : HOLKernelInferenceRules.Rule)
    (nativeArguments : List Preterm) (arguments : InferenceArguments Const gamma rule)
    (parsed : readInferenceArguments (readTermWith extras references constants parameters)
      references names rule (nativeArguments.map (expandEquivalence references abbreviation.reference)) = some arguments)
    (ruleAt : Nat → Option Rule) (selected : ruleAt (rules.index rule) = some (.inference rule))
    (nativeInstance : TheoremInstance)
    (instantiated : TheoremDecl.Instantiates terms context
      (rule.declaration references ids abbreviation.reference) nativeArguments nativeInstance) :
    AdmittedApplication abbreviation theorems context
      (readTermWith extras references constants parameters)
      parameters names ruleAt (rules.index rule) nativeArguments where
  rule := .inference rule
  selected := selected
  native := nativeInstance
  declared := rules.declared rule
  instantiated := instantiated
  operands := .inference arguments
  operands_read := by simp only [readArguments, parsed, Option.map_some]
  premises_read := (read_instance_of_operands faithful abbreviation distinct extras constants parameters
    names rule nativeArguments arguments parsed nativeInstance instantiated).1
  conclusion_read := (read_instance_of_operands faithful abbreviation distinct extras constants parameters
    names rule nativeArguments arguments parsed nativeInstance instantiated).2

end OperandReadback

def contextFormula {rule : HOLKernelInferenceRules.Rule} :
    InferenceArguments Symbol gamma rule → Formula Symbol gamma
  | .truth g => g
  | .contradiction g _ => g
  | .conjunctionIntroduction g _ _ => g
  | .conjunctionLeft g _ _ => g
  | .conjunctionRight g _ _ => g
  | .disjunctionLeft g _ _ => g
  | .disjunctionRight g _ _ => g
  | .disjunctionElimination g _ _ _ => g
  | .implicationIntroduction g _ _ => g
  | .implicationElimination g _ _ => g
  | .negationIntroduction g _ => g
  | .negationElimination g _ => g
  | .reflexivity g _ => g
  | .symmetry g _ _ => g
  | .transitivity g _ _ _ => g
  | .propositionalExtensionality g _ _ => g
  | .equalityImplicationLeft g _ _ => g
  | .equalityImplicationRight g _ _ => g
  | .applicationFunction g _ _ _ => g
  | .applicationArgument g _ _ _ => g
  | .booleanEqualityElimination g _ _ => g

def nativeArguments (references : HOLKernelSyntax.Symbol → Nat)
    (names : Names gamma) (depth : Nat) (antecedent : Preterm)
    {rule : HOLKernelInferenceRules.Rule} (arguments : InferenceArguments Symbol gamma rule) : List Preterm :=
  let code := fun {type} (source : Term Symbol gamma type) => HOLKernelSetOperationReadback.encode references names depth source
  let typeCode := encodeType references HOLKernelSetOperationInterpretation.typeCode
  match arguments with
  | .truth _ => [antecedent]
  | .contradiction _ p => [antecedent, code p]
  | .conjunctionIntroduction _ p q => [antecedent, code p, code q]
  | .conjunctionLeft _ p q => [antecedent, code p, code q]
  | .conjunctionRight _ p q => [antecedent, code p, code q]
  | .disjunctionLeft _ p q => [antecedent, code p, code q]
  | .disjunctionRight _ p q => [antecedent, code p, code q]
  | .disjunctionElimination _ p q r => [antecedent, code p, code q, code r]
  | .implicationIntroduction _ p q => [antecedent, code p, code q]
  | .implicationElimination _ p q => [antecedent, code p, code q]
  | .negationIntroduction _ p => [antecedent, code p]
  | .negationElimination _ p => [antecedent, code p]
  | @InferenceArguments.reflexivity _ _ type _ t => [antecedent, typeCode type, code t]
  | @InferenceArguments.symmetry _ _ type _ t s => [typeCode type, antecedent, code t, code s]
  | @InferenceArguments.transitivity _ _ type _ t s v => [antecedent, typeCode type, code t, code s, code v]
  | .propositionalExtensionality _ p q => [antecedent, code p, code q]
  | .equalityImplicationLeft _ p q => [antecedent, code p, code q]
  | .equalityImplicationRight _ p q => [antecedent, code p, code q]
  | @InferenceArguments.applicationFunction _ _ domain codomain _ t f h => [typeCode domain, typeCode codomain, antecedent, code t, code f, code h]
  | @InferenceArguments.applicationArgument _ _ domain codomain _ t s f => [typeCode domain, typeCode codomain, antecedent, code t, code s, code f]
  | .booleanEqualityElimination _ p q => [antecedent, code p, code q]

variable {sorts : SortSignature} {terms : TermSignature} {definitions : Definition.Signature}
variable {theorems : TheoremSignature} {signature : Signature sorts terms}

theorem read_nativeArguments
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (distinct : ∀ symbol, signature.symbol symbol ≠ abbreviation.reference)
    (names : Names gamma) (depth : Nat) (scope : InScope 7 names depth)
    (antecedent : Preterm) {rule : HOLKernelInferenceRules.Rule}
    (arguments : InferenceArguments Symbol gamma rule)
    (contextRead : readFormulaIn abbreviation
      (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
      7 names antecedent = some (contextFormula arguments)) (nativeInstance : TheoremInstance) :
    readArguments abbreviation
      (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
      7 names (.inference rule) (nativeArguments signature.symbol names depth antecedent arguments) nativeInstance =
      some (RuleArguments.inference arguments) := by
  cases arguments <;>
    simp only [contextFormula, readFormulaIn] at contextRead
  all_goals
    simp [readArguments, nativeArguments, readInferenceArguments,
      expandEquivalence_encodeTerm _ _ distinct,
      expandEquivalence_encodeType _ _ distinct, contextRead,
      logical_reader_encode profile _ names depth scope,
      HOLKernelSetOperationReadback.readType_encode signature.symbol signature.symbol_injective,
      readObjectWith, expect_same]


theorem read_encoded_holds
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (distinct : ∀ symbol, signature.symbol symbol ≠ abbreviation.reference)
    (names : Names gamma) (depth : Nat) (scope : InScope 7 names depth)
    (source : Formula Symbol gamma) :
    readFormulaIn abbreviation
      (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
      7 names (HOLKernelJudgment.holds signature.symbol
        (HOLKernelSetOperationReadback.encode signature.symbol names depth source)) = some source := by
  simp [readFormulaIn, expandEquivalence_holds,
    expandEquivalence_encodeTerm _ _ distinct, readJudgmentWith_holds _ signature.symbol_injective,
    logical_reader_encode profile _ names depth scope, expect_same, Judgment.formula]

theorem read_encoded_typing
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (distinct : ∀ symbol, signature.symbol symbol ≠ abbreviation.reference)
    (names : Names gamma) (depth : Nat) (scope : InScope 7 names depth)
    {type : Ty Unit} (source : Term Symbol gamma type) :
    readFormulaIn abbreviation
      (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
      7 names (HOLKernelJudgment.hasType signature.symbol
        (HOLKernelSetOperationReadback.encode signature.symbol names depth source)
        (encodeType signature.symbol HOLKernelSetOperationInterpretation.typeCode type)) = some .top := by
  simp [readFormulaIn, HOLKernelJudgment.hasType, applySymbol, Preterm.applyArgs,
    expandEquivalence, distinct, expandEquivalence_encodeTerm _ _ distinct,
    expandEquivalence_encodeType _ _ distinct, readJudgmentWith,
    readHead_reference signature.symbol signature.symbol_injective, readTypingWith,
    HOLKernelSetOperationReadback.readType_encode signature.symbol signature.symbol_injective,
    logical_reader_encode profile _ names depth scope, expect_same, Judgment.formula]

theorem read_nativeInstance {context : Context}
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (distinct : ∀ symbol, signature.symbol symbol ≠ abbreviation.reference)
    (names : Names gamma) (depth : Nat) (scope : InScope 7 names depth)
    (antecedent : Preterm) {rule : HOLKernelInferenceRules.Rule}
    (arguments : InferenceArguments Symbol gamma rule)
    (contextRead : readFormulaIn abbreviation
      (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
      7 names antecedent = some (contextFormula arguments))
    (nativeInstance : TheoremInstance)
    (instantiated : TheoremDecl.Instantiates terms context
      (rule.declaration signature.symbol signature.ids abbreviation.reference)
      (nativeArguments signature.symbol names depth antecedent arguments) nativeInstance) :
    nativeInstance.hypotheses.mapM
      (readFormulaIn abbreviation
        (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7) 7 names) =
      some arguments.premises ∧
    readFormulaIn abbreviation
      (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
      7 names nativeInstance.conclusion = some arguments.conclusion := by
  have parsed := read_nativeArguments profile abbreviation distinct names depth scope
    antecedent arguments contextRead nativeInstance
  have operands : readInferenceArguments
      (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
      signature.symbol names rule
      ((nativeArguments signature.symbol names depth antecedent arguments).map
        (expandEquivalence signature.symbol abbreviation.reference)) = some arguments := by
    simpa only [readArguments, Option.map_eq_some_iff,
      RuleArguments.inference.injEq, exists_eq_right] using parsed
  exact read_instance_of_operands signature.symbol_injective abbreviation distinct
    (HOLKernelLogicalFunctionReadback.atoms profile)
    HOLKernelSetOperationReadback.readConstant 7 names rule
    (nativeArguments signature.symbol names depth antecedent arguments) arguments operands
    nativeInstance instantiated


def admittedApplication {context : Context}
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (distinct : ∀ symbol, signature.symbol symbol ≠ abbreviation.reference)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (names : Names gamma) (depth : Nat) (scope : InScope 7 names depth)
    (antecedent : Preterm) {rule : HOLKernelInferenceRules.Rule}
    (arguments : InferenceArguments Symbol gamma rule)
    (contextRead : readFormulaIn abbreviation
      (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
      7 names antecedent = some (contextFormula arguments))
    (ruleAt : Nat → Option Rule) (selected : ruleAt (rules.index rule) = some (.inference rule))
    (nativeInstance : TheoremInstance)
    (instantiated : TheoremDecl.Instantiates terms context
      (rule.declaration signature.symbol signature.ids abbreviation.reference)
      (nativeArguments signature.symbol names depth antecedent arguments) nativeInstance) :
    AdmittedApplication abbreviation theorems context
      (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
      7 names ruleAt (rules.index rule)
      (nativeArguments signature.symbol names depth antecedent arguments) := by
  have parsed : readInferenceArguments
      (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
      signature.symbol names rule
      ((nativeArguments signature.symbol names depth antecedent arguments).map
        (expandEquivalence signature.symbol abbreviation.reference)) = some arguments := by
    simpa only [readArguments, Option.map_eq_some_iff,
      RuleArguments.inference.injEq, exists_eq_right] using
      read_nativeArguments profile abbreviation distinct names depth scope
        antecedent arguments contextRead nativeInstance
  exact admittedApplicationOfOperands signature.symbol_injective abbreviation distinct
    (HOLKernelLogicalFunctionReadback.atoms profile)
    HOLKernelSetOperationReadback.readConstant 7 rules names rule
    (nativeArguments signature.symbol names depth antecedent arguments) arguments parsed
    ruleAt selected nativeInstance instantiated


theorem application_admitted {context : Context}
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (distinct : ∀ symbol, signature.symbol symbol ≠ abbreviation.reference)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (names : Names gamma) (depth : Nat) (scope : InScope 7 names depth)
    (antecedent : Preterm) {rule : HOLKernelInferenceRules.Rule}
    (arguments : InferenceArguments Symbol gamma rule)
    (contextRead : readFormulaIn abbreviation
      (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
      7 names antecedent = some (contextFormula arguments))
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (selected : ruleAt (rules.index rule) = some (.inference rule))
    (nativeInstance : TheoremInstance)
    (instantiated : TheoremDecl.Instantiates terms context
      (rule.declaration signature.symbol signature.ids abbreviation.reference)
      (nativeArguments signature.symbol names depth antecedent arguments) nativeInstance)
    (children : List ProofWitness)
    (checked : ProofWitness.Checks terms definitions theorems context []
      (.theoremApp (rules.index rule)
        (nativeArguments signature.symbol names depth antecedent arguments) children)
      nativeInstance.conclusion)
    (fuel : Nat)
    (childrenAdmitted : HOLKernelProofReadback.AdmittedChildren
      (fun child formula => HOLKernelProofReadback.AdmittedProof abbreviation theorems context
        (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
        7 ruleAt bindingAt fuel names child formula) children arguments.premises) :
    Nonempty (HOLKernelProofReadback.AdmittedProof abbreviation theorems context
      (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
      7 ruleAt bindingAt (fuel + 1) names
      (.theoremApp (rules.index rule)
        (nativeArguments signature.symbol names depth antecedent arguments) children)
      arguments.conclusion) :=
  ⟨HOLKernelProofReadback.AdmittedStep.application checked.eval
    (admittedApplication profile abbreviation distinct rules names depth scope antecedent arguments contextRead
      ruleAt selected nativeInstance instantiated) rfl childrenAdmitted⟩

#print axioms read_instance_of_operands
#print axioms admittedApplicationOfOperands
#print axioms admittedApplication
#print axioms application_admitted

#print axioms read_nativeInstance

#print axioms read_nativeArguments
end Mettapedia.Languages.MM0.HOLKernelInferenceReadback

