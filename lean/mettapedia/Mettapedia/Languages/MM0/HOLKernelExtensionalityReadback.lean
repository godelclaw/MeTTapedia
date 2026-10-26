import Mettapedia.Languages.MM0.HOLKernelExtensionality
import Mettapedia.Languages.MM0.HOLKernelLogicalCongruenceReadback
import Mettapedia.Languages.MM0.HOLKernelQuantifierReadback

/-!
# Admission of native function extensionality

The actual maintained-HOL construction specializes the pointwise premise at a
second fresh variable, abstracts the resulting equation, and joins two native
eta receipts. Its substitution comparison uses the existing application and
equality congruence constructors. The returned native witness is unchanged.

The retained pointwise certificate must be independently admitted in the fresh
argument frame. This is an explicit premise: admission in the original frame
alone does not imply arbitrary fresh-frame transport of internal binders.
Successful operand readings, dictionary freshness, native occurrence conditions
and the exact theorem-selection policy remain explicit.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.MM0.HOLKernelExtensionalityReadback
open Mettapedia.Logic Mettapedia.Logic.HOL
open Kernel HOLKernelSyntax HOLKernelJudgment
open HOLKernelTermReadback HOLKernelJudgmentReadback HOLKernelRuleReadback HOLKernelProofReadback
open HOLKernelTypingRules (typed boolType functionType)
open HOLKernelInferenceRules (equality)
open HOLKernelStructuralRules (CheckedProof)
open NamedElaboration (BinderNames)
universe u
variable {Const : Ty Unit → Type u} {gamma : Ctx Unit}
variable {sorts : SortSignature} {terms : TermSignature} {definitions : Definition.Signature}
variable {theorems : TheoremSignature} {context : Context}
theorem functionExtensionality_admitted (signature : Signature sorts terms)
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : HOLKernelTypingRules.Rules theorems signature.symbol signature.ids)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (antecedent domain result first second : Preterm) (quantified argument : Nat)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (domainSorted : Preterm.HasType terms context domain [] signature.ids.type)
    (resultSorted : Preterm.HasType terms context result [] signature.ids.type)
    (firstSorted : Preterm.HasType terms context first [] signature.ids.object)
    (secondSorted : Preterm.HasType terms context second [] signature.ids.object)
    (quantifiedBound : context[quantified]? = some (.bound signature.ids.object))
    (argumentBound : context[argument]? = some (.bound signature.ids.object))
    (different : quantified ≠ argument)
    (antecedentQuantifiedIndependent : ¬ Preterm.HasVar context quantified antecedent)
    (antecedentArgumentIndependent : ¬ Preterm.HasVar context argument antecedent)
    (domainQuantifiedIndependent : ¬ Preterm.HasVar context quantified domain)
    (domainArgumentIndependent : ¬ Preterm.HasVar context argument domain)
    (resultArgumentIndependent : ¬ Preterm.HasVar context argument result)
    (firstTyping : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := [])
      (typed signature.symbol antecedent first (functionType signature.symbol domain result)))
    (secondTyping : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := [])
      (typed signature.symbol antecedent second (functionType signature.symbol domain result)))
    (pointwise : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := [])
      (entails signature.symbol antecedent (holds signature.symbol (applySymbol signature.symbol .allc
        [.var quantified, domain, equality signature.symbol result
          (applySymbol signature.symbol .app [first, .var quantified])
          (applySymbol signature.symbol .app [second, .var quantified])]))))

    (distinct : ∀ symbol, signature.symbol symbol ≠ abbreviation.reference)
    (dictionary : Nat → Option (NamedElaboration.SomeConst Const)) (parameters : Nat) (names : Names gamma)
    (domainType resultType : Ty Unit) (f g : Term Const gamma (domainType ⇒ resultType)) (antecedentMeaning : Judgment Const gamma)
    (antecedentRead : readJudgmentWith (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) signature.symbol names
      (expandEquivalence signature.symbol abbreviation.reference antecedent) = some antecedentMeaning)
    (domainRead : readType signature.symbol (expandEquivalence signature.symbol abbreviation.reference domain) = some domainType)
    (resultRead : readType signature.symbol (expandEquivalence signature.symbol abbreviation.reference result) = some resultType)
    (firstRead : HOLKernelLogicalFunctionReadback.reader profile dictionary parameters names
      (expandEquivalence signature.symbol abbreviation.reference first) = some ⟨domainType ⇒ resultType, f⟩)
    (secondRead : HOLKernelLogicalFunctionReadback.reader profile dictionary parameters names
      (expandEquivalence signature.symbol abbreviation.reference second) = some ⟨domainType ⇒ resultType, g⟩)
    (quantifiedFresh : HOLKernelBindingInterpretation.freshName parameters names quantified = true)
    (argumentFresh : HOLKernelBindingInterpretation.freshName parameters names argument = true)
    (quantifiedDictionary : dictionary quantified = none) (argumentDictionary : dictionary argument = none)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (selected : ∀ rule, ruleAt (rules.index rule) = some (.inference rule))
    (structuralSelected : ∀ rule, ruleAt (structural.index rule) = some (.structural rule))
    (bindingSelected : ∀ rule, bindingAt (binding.index rule) = some rule)
    {pointwiseFuel : Nat}
    (pointwiseAdmitted : AdmittedProof abbreviation theorems context
      (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) parameters ruleAt bindingAt pointwiseFuel
      (BinderNames.cons (type := domainType) argument names) pointwise.val
      (.imp (weaken (σ := domainType) antecedentMeaning.formula)
        (.all (.eq (.app (weaken (σ := domainType) (weaken (σ := domainType) f)) (.var .vz))
          (.app (weaken (σ := domainType) (weaken (σ := domainType) g)) (.var .vz)))))) :
    ∃ fuel, Nonempty (AdmittedProof abbreviation theorems context
      (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) parameters ruleAt bindingAt fuel names
      (HOLKernelExtensionality.functionExtensionality signature abbreviation profile structural typing rules binding antecedent domain result first second quantified argument
        antecedentSorted domainSorted resultSorted firstSorted secondSorted quantifiedBound argumentBound different
        antecedentQuantifiedIndependent antecedentArgumentIndependent domainQuantifiedIndependent domainArgumentIndependent resultArgumentIndependent
        firstTyping secondTyping pointwise).val (.imp antecedentMeaning.formula (.eq f g))) := by
  have quantifiedSorted : Preterm.HasType terms context (.var quantified) [] signature.ids.object :=
    .var (binder := .bound signature.ids.object) quantifiedBound
  have argumentSorted : Preterm.HasType terms context (.var argument) [] signature.ids.object :=
    .var (binder := .bound signature.ids.object) argumentBound
  have typeSorted := signature.application context .function [domain, result]
    (.cons (.regular domainSorted) (.cons (.regular resultSorted) .nil))
  let extra := hasType signature.symbol (.var argument) domain
  have extraSorted := hasType_sorted signature context argumentSorted domainSorted
  let extended := conjunction signature.symbol antecedent extra
  have extendedSorted := conjunction_sorted signature context antecedentSorted extraSorted
  let argumentTyping := HOLKernelStructuralRules.right (definitions := definitions) (hypotheses := []) signature structural antecedent extra antecedentSorted extraSorted
  let firstExtended := HOLKernelStructuralRules.weaken signature structural antecedent extra _ antecedentSorted extraSorted
    (hasType_sorted signature context firstSorted typeSorted) firstTyping
  let secondExtended := HOLKernelStructuralRules.weaken signature structural antecedent extra _ antecedentSorted extraSorted
    (hasType_sorted signature context secondSorted typeSorted) secondTyping
  have firstQuantifiedSorted := signature.application context .app _
    (.cons (.regular firstSorted) (.cons (.regular quantifiedSorted) .nil))
  have firstArgumentSorted := signature.application context .app _
    (.cons (.regular firstSorted) (.cons (.regular argumentSorted) .nil))
  have secondQuantifiedSorted := signature.application context .app _
    (.cons (.regular secondSorted) (.cons (.regular quantifiedSorted) .nil))
  have secondArgumentSorted := signature.application context .app _
    (.cons (.regular secondSorted) (.cons (.regular argumentSorted) .nil))
  let firstApplication := HOLKernelTypingProofs.applicationTyping signature typing extended domain result first (.var argument)
    extendedSorted domainSorted resultSorted firstSorted argumentSorted firstExtended argumentTyping
  let secondApplication := HOLKernelTypingProofs.applicationTyping signature typing extended domain result second (.var argument)
    extendedSorted domainSorted resultSorted secondSorted argumentSorted secondExtended argumentTyping
  let resultTyping := HOLKernelTypingProofs.equalityTyping signature typing result extended _ _ resultSorted extendedSorted
    firstArgumentSorted secondArgumentSorted firstApplication secondApplication
  let body := equality signature.symbol result
    (applySymbol signature.symbol .app [first, .var quantified])
    (applySymbol signature.symbol .app [second, .var quantified])
  let instantiated := equality signature.symbol result
    (applySymbol signature.symbol .app [first, .var argument])
    (applySymbol signature.symbol .app [second, .var argument])
  have bodySorted := signature.application context .eqc _
    (.cons (.regular resultSorted) (.cons (.regular firstQuantifiedSorted) (.cons (.regular secondQuantifiedSorted) .nil)))
  have instantiatedSorted := signature.application context .eqc _
    (.cons (.regular resultSorted) (.cons (.regular firstArgumentSorted) (.cons (.regular secondArgumentSorted) .nil)))
  let equation := holds signature.symbol (equality signature.symbol domain (.var quantified) (.var argument))
  have equationSorted := holds_sorted signature context (signature.application context .eqc _
    (.cons (.regular domainSorted) (.cons (.regular quantifiedSorted) (.cons (.regular argumentSorted) .nil))))
  let equationContext := conjunction signature.symbol extended equation
  have equationContextSorted := conjunction_sorted signature context extendedSorted equationSorted
  let variableEquation := HOLKernelStructuralRules.right (definitions := definitions) (hypotheses := []) signature structural extended equation extendedSorted equationSorted
  let firstUnderEquation := HOLKernelStructuralRules.weaken signature structural extended equation _ extendedSorted equationSorted
    (hasType_sorted signature context firstSorted typeSorted) firstExtended
  let secondUnderEquation := HOLKernelStructuralRules.weaken signature structural extended equation _ extendedSorted equationSorted
    (hasType_sorted signature context secondSorted typeSorted) secondExtended
  let firstEquation := HOLKernelInferenceProofs.Native.applicationArgument signature rules domain result equationContext _ _ first
    domainSorted resultSorted equationContextSorted quantifiedSorted argumentSorted firstSorted firstUnderEquation variableEquation
  let secondEquation := HOLKernelInferenceProofs.Native.applicationArgument signature rules domain result equationContext _ _ second
    domainSorted resultSorted equationContextSorted quantifiedSorted argumentSorted secondSorted secondUnderEquation variableEquation
  let substitution := HOLKernelCongruence.equalityCongruence signature profile rules binding equationContext result _ _ _ _
    equationContextSorted resultSorted firstQuantifiedSorted firstArgumentSorted secondQuantifiedSorted secondArgumentSorted
    firstEquation secondEquation
  have quantifiedFormulaSorted := signature.application context .allc _
    (.cons (.bound quantifiedBound) (.cons (.regular domainSorted) (.cons (.regular bodySorted) .nil)))
  let weakenedPointwise := HOLKernelStructuralRules.weaken signature structural antecedent extra _ antecedentSorted extraSorted
    (holds_sorted signature context quantifiedFormulaSorted) pointwise
  have extendedIndependent := HOLKernelTypeSupport.contextExtension_independent context quantified argument signature.ids.object
    signature.symbol antecedent domain argumentBound different antecedentQuantifiedIndependent domainQuantifiedIndependent
  let pointwiseAtArgument := HOLKernelQuantifierProofs.universalElimination signature abbreviation binding extended domain
    (.var argument) body instantiated quantified extendedSorted domainSorted quantifiedBound argumentSorted bodySorted instantiatedSorted
    extendedIndependent domainQuantifiedIndependent argumentTyping resultTyping substitution weakenedPointwise
  let abstraction := HOLKernelBindingProofs.Native.abstractionCongruence signature binding antecedent domain result argument _ _
    antecedentSorted domainSorted resultSorted argumentBound firstArgumentSorted secondArgumentSorted
    antecedentArgumentIndependent domainArgumentIndependent resultArgumentIndependent pointwiseAtArgument
  let firstEta := HOLKernelBindingProofs.Native.eta signature binding antecedent domain result argument first
    antecedentSorted domainSorted resultSorted argumentBound firstSorted antecedentArgumentIndependent
    domainArgumentIndependent resultArgumentIndependent firstTyping
  let secondEta := HOLKernelBindingProofs.Native.eta signature binding antecedent domain result argument second
    antecedentSorted domainSorted resultSorted argumentBound secondSorted antecedentArgumentIndependent
    domainArgumentIndependent resultArgumentIndependent secondTyping
  have firstLambdaSorted := signature.application context .lam _
    (.cons (.bound argumentBound) (.cons (.regular domainSorted) (.cons (.regular firstArgumentSorted) .nil)))
  have secondLambdaSorted := signature.application context .lam _
    (.cons (.bound argumentBound) (.cons (.regular domainSorted) (.cons (.regular secondArgumentSorted) .nil)))
  let firstBack := HOLKernelInferenceProofs.Native.symmetry signature rules _ antecedent _ _ typeSorted antecedentSorted
    firstLambdaSorted firstSorted firstEta
  let joined := HOLKernelInferenceProofs.Native.transitivity signature rules antecedent _ _ _ _ antecedentSorted typeSorted
    firstSorted firstLambdaSorted secondLambdaSorted firstBack abstraction

  let argumentNames : Names (domainType :: gamma) := BinderNames.cons argument names
  let quantifiedNames : Names (domainType :: domainType :: gamma) := BinderNames.cons quantified argumentNames
  have argumentAbove : parameters ≤ argument := by
    have h := argumentFresh
    simp only [HOLKernelBindingInterpretation.freshName, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1
  have quantifiedAbove : parameters ≤ quantified := by
    have h := quantifiedFresh
    simp only [HOLKernelBindingInterpretation.freshName, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1
  have argumentAbsent : names.lookup? argument = none := by
    have h := argumentFresh
    simp only [HOLKernelBindingInterpretation.freshName, Bool.and_eq_true, decide_eq_true_eq] at h
    simpa using h.2
  have quantifiedAbsent : names.lookup? quantified = none := by
    have h := quantifiedFresh
    simp only [HOLKernelBindingInterpretation.freshName, Bool.and_eq_true, decide_eq_true_eq] at h
    simpa using h.2
  have quantifiedAbsentNext : argumentNames.lookup? quantified = none := by
    simp [argumentNames, BinderNames.lookup?_cons_of_ne different.symm, quantifiedAbsent]
  have argumentLookup : LookupPreserving dictionary (Rename.weaken (σ := domainType)) names argumentNames :=
    LookupPreserving.weaken dictionary names domainType argument argumentAbsent argumentDictionary
  have quantifiedLookup : LookupPreserving dictionary (Rename.weaken (σ := domainType)) argumentNames quantifiedNames :=
    LookupPreserving.weaken dictionary argumentNames domainType quantified quantifiedAbsentNext quantifiedDictionary
  have firstAtArgument := logical_reader_rename_of_read profile dictionary parameters names argumentNames
    (Rename.weaken (σ := domainType)) argumentLookup _ f firstRead
  have secondAtArgument := logical_reader_rename_of_read profile dictionary parameters names argumentNames
    (Rename.weaken (σ := domainType)) argumentLookup _ g secondRead
  have firstAtQuantified := logical_reader_rename_of_read profile dictionary parameters argumentNames quantifiedNames
    (Rename.weaken (σ := domainType)) quantifiedLookup _ (weaken (σ := domainType) f) firstAtArgument
  have secondAtQuantified := logical_reader_rename_of_read profile dictionary parameters argumentNames quantifiedNames
    (Rename.weaken (σ := domainType)) quantifiedLookup _ (weaken (σ := domainType) g) secondAtArgument
  have antecedentAtArgument := logical_judgment_rename_of_read profile dictionary parameters names argumentNames
    (Rename.weaken (σ := domainType)) argumentLookup _ antecedentMeaning antecedentRead
  have argumentVariableRead : (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) argumentNames ((expandEquivalence signature.symbol abbreviation.reference) (.var argument)) = some ⟨domainType, Term.var .vz⟩ := by
    simp [HOLKernelLogicalFunctionReadback.reader, HOLKernelLogicalFunctionReadback.reader, readTermWith, readVariable, expandEquivalence, argumentNames]
  have quantifiedVariableRead : (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) quantifiedNames ((expandEquivalence signature.symbol abbreviation.reference) (.var quantified)) = some ⟨domainType, Term.var .vz⟩ := by
    simp [HOLKernelLogicalFunctionReadback.reader, HOLKernelLogicalFunctionReadback.reader, readTermWith, readVariable, expandEquivalence, quantifiedNames]
  have argumentVariableAtQuantified : (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) quantifiedNames ((expandEquivalence signature.symbol abbreviation.reference) (.var argument)) = some ⟨domainType, Term.var (.vs .vz)⟩ := by
    simp [HOLKernelLogicalFunctionReadback.reader, HOLKernelLogicalFunctionReadback.reader, readTermWith, readVariable, expandEquivalence,
      quantifiedNames, argumentNames, BinderNames.lookup?_cons_of_ne different]
  have appRead {delta : Ctx Unit} (frame : Names delta) {dom cod : Ty Unit} (nativeFunction nativeArgument : Preterm)
      (function : Term Const delta (dom ⇒ cod)) (value : Term Const delta dom)
      (functionRead : (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) frame ((expandEquivalence signature.symbol abbreviation.reference) nativeFunction) = some ⟨dom ⇒ cod, function⟩)
      (valueRead : (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) frame ((expandEquivalence signature.symbol abbreviation.reference) nativeArgument) = some ⟨dom, value⟩) :
      (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) frame ((expandEquivalence signature.symbol abbreviation.reference) (applySymbol signature.symbol .app [nativeFunction, nativeArgument])) = some ⟨cod, Term.app function value⟩ := by
    simpa only [HOLKernelLogicalFunctionReadback.reader, applySymbol, Preterm.applyArgs, expandEquivalence, if_neg (distinct .app)] using
      readTermWith_application (HOLKernelLogicalFunctionReadback.atoms profile) signature.symbol signature.symbol_injective dictionary parameters
        frame _ _ function value functionRead valueRead
  have eqRead {delta : Ctx Unit} (frame : Names delta) (typeCode left right : Preterm) {type : Ty Unit}
      (leftTerm rightTerm : Term Const delta type)
      (typeRead : readType signature.symbol ((expandEquivalence signature.symbol abbreviation.reference) typeCode) = some type)
      (leftRead : (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) frame ((expandEquivalence signature.symbol abbreviation.reference) left) = some ⟨type, leftTerm⟩) (rightRead : (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) frame ((expandEquivalence signature.symbol abbreviation.reference) right) = some ⟨type, rightTerm⟩) :
      (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) frame ((expandEquivalence signature.symbol abbreviation.reference) (equality signature.symbol typeCode left right)) = some ⟨.prop, Term.eq leftTerm rightTerm⟩ := by
    simpa only [HOLKernelLogicalFunctionReadback.reader, HOLKernelInferenceRules.equality, applySymbol, Preterm.applyArgs, expandEquivalence, if_neg (distinct .eqc)] using
      readTermWith_equality (HOLKernelLogicalFunctionReadback.atoms profile) signature.symbol signature.symbol_injective dictionary parameters
        frame _ _ _ type leftTerm rightTerm typeRead leftRead rightRead
  have holdsRead {delta : Ctx Unit} (frame : Names delta) (native : Preterm) (formula : Formula Const delta)
      (reading : (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) frame ((expandEquivalence signature.symbol abbreviation.reference) native) = some ⟨.prop, formula⟩) : readFormulaIn abbreviation (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) parameters frame (holds signature.symbol native) = some formula := by
    simp [readFormulaIn, holds, applySymbol, Preterm.applyArgs, expandEquivalence, readJudgmentWith,
      readHead_reference signature.symbol signature.symbol_injective, reading, expect_same, Judgment.formula]
  have firstArgumentRead := appRead argumentNames first (.var argument) (weaken (σ := domainType) f) (.var .vz) firstAtArgument argumentVariableRead
  have secondArgumentRead := appRead argumentNames second (.var argument) (weaken (σ := domainType) g) (.var .vz) secondAtArgument argumentVariableRead
  have firstQuantifiedRead := appRead quantifiedNames first (.var quantified) (weaken (σ := domainType) (weaken (σ := domainType) f)) (.var .vz) firstAtQuantified quantifiedVariableRead
  have secondQuantifiedRead := appRead quantifiedNames second (.var quantified) (weaken (σ := domainType) (weaken (σ := domainType) g)) (.var .vz) secondAtQuantified quantifiedVariableRead
  have firstArgumentReadTwice := appRead quantifiedNames first (.var argument) (weaken (σ := domainType) (weaken (σ := domainType) f)) (.var (.vs .vz)) firstAtQuantified argumentVariableAtQuantified
  have secondArgumentReadTwice := appRead quantifiedNames second (.var argument) (weaken (σ := domainType) (weaken (σ := domainType) g)) (.var (.vs .vz)) secondAtQuantified argumentVariableAtQuantified
  let firstBody : Term Const (domainType :: gamma) resultType := .app (weaken (σ := domainType) f) (.var .vz)
  let secondBody : Term Const (domainType :: gamma) resultType := .app (weaken (σ := domainType) g) (.var .vz)
  let predicate : Formula Const (domainType :: domainType :: gamma) :=
    .eq (.app (weaken (σ := domainType) (weaken (σ := domainType) f)) (.var .vz))
      (.app (weaken (σ := domainType) (weaken (σ := domainType) g)) (.var .vz))
  have bodyRead : (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) quantifiedNames ((expandEquivalence signature.symbol abbreviation.reference) body) = some ⟨.prop, predicate⟩ :=
    eqRead quantifiedNames result _ _ _ _ resultRead firstQuantifiedRead secondQuantifiedRead
  have instantiatedRead : (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) argumentNames ((expandEquivalence signature.symbol abbreviation.reference) instantiated) = some ⟨.prop, Term.eq firstBody secondBody⟩ :=
    eqRead argumentNames result _ _ firstBody secondBody resultRead firstArgumentRead secondArgumentRead
  let argumentMeaning : Judgment Const (domainType :: gamma) := .conjunction
    (antecedentMeaning.rename (Rename.weaken (σ := domainType))) (.typing (.var .vz))
  simp only [expandEquivalence] at argumentVariableRead
  have extraRead : readJudgmentWith (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) signature.symbol argumentNames ((expandEquivalence signature.symbol abbreviation.reference) extra) = some (.typing (Term.var (.vz : Var (domainType :: gamma) domainType))) := by
    simp [extra, hasType, applySymbol, Preterm.applyArgs, expandEquivalence, distinct, readJudgmentWith,
      readHead_reference signature.symbol signature.symbol_injective, readTypingWith, domainRead, argumentVariableRead, expect_same]
  have extendedRead : readJudgmentWith (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) signature.symbol argumentNames ((expandEquivalence signature.symbol abbreviation.reference) extended) = some argumentMeaning := by
    simp [extended, conjunction, applySymbol, Preterm.applyArgs, expandEquivalence, distinct, readJudgmentWith,
      readHead_reference signature.symbol signature.symbol_injective, antecedentAtArgument, extraRead, argumentMeaning]
  have extendedReadTwice := logical_judgment_rename_of_read profile dictionary parameters argumentNames quantifiedNames
    (Rename.weaken (σ := domainType)) quantifiedLookup _ argumentMeaning extendedRead
  let equationMeaning : Judgment Const (domainType :: domainType :: gamma) := .assertion (.eq (.var .vz) (.var (.vs .vz)))
  let equationContextMeaning : Judgment Const (domainType :: domainType :: gamma) :=
    .conjunction (argumentMeaning.rename (Rename.weaken (σ := domainType))) equationMeaning
  have equationRead : readJudgmentWith (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) signature.symbol quantifiedNames ((expandEquivalence signature.symbol abbreviation.reference) equation) = some equationMeaning :=
    HOLKernelCongruenceReadback.equation_judgment_read signature abbreviation profile distinct dictionary parameters quantifiedNames
      domain _ _ (.var .vz) (.var (.vs .vz)) domainRead quantifiedVariableRead argumentVariableAtQuantified
  have equationContextRead : readJudgmentWith (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) signature.symbol quantifiedNames ((expandEquivalence signature.symbol abbreviation.reference) equationContext) = some equationContextMeaning := by
    simp [equationContext, conjunction, applySymbol, Preterm.applyArgs, expandEquivalence, distinct, readJudgmentWith,
      readHead_reference signature.symbol signature.symbol_injective, extendedReadTwice, equationRead, equationContextMeaning]
  obtain ⟨variableTree⟩ := HOLKernelStructuralReadback.right_admitted signature abbreviation (distinct .im) (distinct .an) structural (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) parameters quantifiedNames ruleAt bindingAt
    (structuralSelected .anr) extended equation extendedSorted equationSorted
    (argumentMeaning.rename (Rename.weaken (σ := domainType))).formula equationMeaning.formula
    (by simp only [readFormulaIn, extendedReadTwice, Option.map_some]) (by simp only [readFormulaIn, equationRead, Option.map_some])
  obtain ⟨firstTree⟩ := HOLKernelCongruenceReadback.applicationArgument_admitted signature abbreviation profile distinct dictionary parameters rules quantifiedNames
    domain result equationContext _ _ first domainSorted resultSorted equationContextSorted quantifiedSorted argumentSorted firstSorted firstUnderEquation variableEquation
    equationContextMeaning (.var .vz) (.var (.vs .vz)) (weaken (σ := domainType) (weaken (σ := domainType) f)) equationContextRead domainRead resultRead
    quantifiedVariableRead argumentVariableAtQuantified firstAtQuantified ruleAt bindingAt (selected .applicationArgument) variableTree
  obtain ⟨secondTree⟩ := HOLKernelCongruenceReadback.applicationArgument_admitted signature abbreviation profile distinct dictionary parameters rules quantifiedNames
    domain result equationContext _ _ second domainSorted resultSorted equationContextSorted quantifiedSorted argumentSorted secondSorted secondUnderEquation variableEquation
    equationContextMeaning (.var .vz) (.var (.vs .vz)) (weaken (σ := domainType) (weaken (σ := domainType) g)) equationContextRead domainRead resultRead
    quantifiedVariableRead argumentVariableAtQuantified secondAtQuantified ruleAt bindingAt (selected .applicationArgument) variableTree
  obtain ⟨substitutionFuel, ⟨substitutionTree⟩⟩ := HOLKernelCongruenceReadback.equality_admitted signature abbreviation profile distinct dictionary parameters rules binding quantifiedNames
    equationContext result _ _ _ _ equationContextSorted resultSorted firstQuantifiedSorted firstArgumentSorted secondQuantifiedSorted secondArgumentSorted firstEquation secondEquation
    equationContextMeaning _ _ _ _ resultRead equationContextRead firstQuantifiedRead firstArgumentReadTwice secondQuantifiedRead secondArgumentReadTwice
    ruleAt bindingAt selected firstTree secondTree
  have quantifiedRead : (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) argumentNames ((expandEquivalence signature.symbol abbreviation.reference) (applySymbol signature.symbol .allc [.var quantified, domain, body])) = some ⟨.prop, Term.all predicate⟩ := by
    simpa only [HOLKernelLogicalFunctionReadback.reader, applySymbol, Preterm.applyArgs, expandEquivalence, if_neg (distinct .allc)] using
      readTermWith_universal (HOLKernelLogicalFunctionReadback.atoms profile) signature.symbol signature.symbol_injective dictionary parameters argumentNames
        _ _ domainType quantified predicate quantifiedAbove domainRead bodyRead
  obtain ⟨weakenedPointwiseTree⟩ := HOLKernelStructuralReadback.weaken_admitted signature abbreviation (distinct .im) (distinct .an) structural (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) parameters argumentNames
    ruleAt bindingAt structuralSelected antecedent extra _ antecedentSorted extraSorted (holds_sorted signature context quantifiedFormulaSorted) pointwise
    (weaken (σ := domainType) antecedentMeaning.formula) .top (.all predicate)
    (by simp only [readFormulaIn, antecedentAtArgument, Option.map_some, Judgment.rename_formula]; rfl)
    (by simp only [readFormulaIn, extraRead, Option.map_some, Judgment.formula])
    (holdsRead argumentNames _ (.all predicate) quantifiedRead) pointwiseAdmitted
  have quantifiedFreshNext : HOLKernelBindingInterpretation.freshName parameters argumentNames quantified = true := by
    simp [HOLKernelBindingInterpretation.freshName, quantifiedAbove, quantifiedAbsentNext]
  have substitutionTree' : AdmittedProof abbreviation theorems context (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) parameters ruleAt bindingAt substitutionFuel quantifiedNames substitution.val
      (.imp (.and (weaken (σ := domainType) argumentMeaning.formula) (.eq (.var .vz) (weaken (σ := domainType) (Term.var (.vz : Var (domainType :: gamma) domainType)))))
        (.eq predicate (weaken (σ := domainType) (Term.eq firstBody secondBody)))) := by
    simpa only [equationContextMeaning, equationMeaning, Judgment.formula, Judgment.rename_formula, firstBody, secondBody, predicate, weaken, HOL.rename, rename_comp, Rename.weaken] using substitutionTree
  obtain ⟨pointwiseTree⟩ := HOLKernelQuantifierReadback.universalElimination_admitted signature abbreviation binding extended domain (.var argument) body instantiated quantified
    extendedSorted domainSorted quantifiedBound argumentSorted bodySorted instantiatedSorted extendedIndependent domainQuantifiedIndependent
    argumentTyping resultTyping substitution weakenedPointwise profile distinct dictionary parameters argumentNames domainType (.var .vz) predicate (.eq firstBody secondBody)
    argumentMeaning extendedRead domainRead (by simpa only [expandEquivalence] using argumentVariableRead) bodyRead instantiatedRead quantifiedFreshNext quantifiedDictionary ruleAt bindingAt
    (bindingSelected .universalElimination) substitutionTree'
    (by simpa only [argumentMeaning, Judgment.formula, Judgment.rename_formula, weaken] using weakenedPointwiseTree)
  have typeRead : readType signature.symbol ((expandEquivalence signature.symbol abbreviation.reference) (functionType signature.symbol domain result)) = some (domainType ⇒ resultType) := by
    simp [functionType, applySymbol, Preterm.applyArgs, expandEquivalence, distinct, readType,
      readHead_reference signature.symbol signature.symbol_injective, domainRead, resultRead]
  have lambdaRead (native : Preterm) (term : Term Const gamma (domainType ⇒ resultType))
      (nativeRead : (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) argumentNames ((expandEquivalence signature.symbol abbreviation.reference) (applySymbol signature.symbol .app [native, .var argument])) = some ⟨resultType, Term.app (weaken (σ := domainType) term) (.var .vz)⟩) :
      (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) names ((expandEquivalence signature.symbol abbreviation.reference) (applySymbol signature.symbol .lam [.var argument, domain, applySymbol signature.symbol .app [native, .var argument]])) =
        some ⟨domainType ⇒ resultType, Term.lam (.app (weaken (σ := domainType) term) (.var .vz))⟩ := by
    simpa only [HOLKernelLogicalFunctionReadback.reader, applySymbol, Preterm.applyArgs, expandEquivalence, if_neg (distinct .lam)] using
      readTermWith_lambda (HOLKernelLogicalFunctionReadback.atoms profile) signature.symbol signature.symbol_injective dictionary parameters names
        _ _ domainType resultType argument (.app (weaken (σ := domainType) term) (.var .vz)) argumentAbove domainRead nativeRead
  have firstLambdaRead := lambdaRead first f firstArgumentRead
  have secondLambdaRead := lambdaRead second g secondArgumentRead
  have implicationRead {firstNative secondNative : Preterm} (left right : Term Const gamma (domainType ⇒ resultType))
      (leftRead : (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) names ((expandEquivalence signature.symbol abbreviation.reference) firstNative) = some ⟨domainType ⇒ resultType, left⟩)
      (rightRead : (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) names ((expandEquivalence signature.symbol abbreviation.reference) secondNative) = some ⟨domainType ⇒ resultType, right⟩) :
      readFormulaIn abbreviation (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) parameters names (entails signature.symbol antecedent
        (holds signature.symbol (equality signature.symbol (functionType signature.symbol domain result) firstNative secondNative))) =
      some (.imp antecedentMeaning.formula (.eq left right)) := by
    rw [HOLKernelStructuralReadback.read_entails abbreviation signature.symbol_injective (distinct .im)]
    have leftAntecedent : readFormulaIn abbreviation (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) parameters names antecedent = some antecedentMeaning.formula := by
      simp only [readFormulaIn, antecedentRead, Option.map_some]
    rw [leftAntecedent, HOLKernelCongruenceReadback.equation_read signature abbreviation profile distinct dictionary parameters names
      _ _ _ left right typeRead leftRead rightRead]
    rfl
  let abstractionTree : AdmittedProof abbreviation theorems context (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) parameters ruleAt bindingAt
      (max (max 1 pointwiseFuel + 1) (substitutionFuel + 1) + 1 + 1) names abstraction.val
      (.imp antecedentMeaning.formula (.eq (.lam firstBody) (.lam secondBody))) :=
    AdmittedStep.binding abstraction.property.eval {
      rule := .abstractionCongruence
      selected := bindingSelected .abstractionCongruence
      declared := binding.declared .abstractionCongruence
      conclusion_read := implicationRead (.lam firstBody) (.lam secondBody) firstLambdaRead secondLambdaRead
      step := .abstractionCongruence argumentFresh (by simpa only [argumentMeaning, Judgment.formula, Judgment.rename_formula, weaken] using pointwiseTree) }
  let firstEtaTree : AdmittedProof abbreviation theorems context (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) parameters ruleAt bindingAt 1 names firstEta.val
      (.imp antecedentMeaning.formula (.eq (.lam firstBody) f)) :=
    AdmittedStep.binding firstEta.property.eval {
      rule := .eta
      selected := bindingSelected .eta
      declared := binding.declared .eta
      conclusion_read := implicationRead (.lam firstBody) f firstLambdaRead firstRead
      step := .eta }
  let secondEtaTree : AdmittedProof abbreviation theorems context (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) parameters ruleAt bindingAt 1 names secondEta.val
      (.imp antecedentMeaning.formula (.eq (.lam secondBody) g)) :=
    AdmittedStep.binding secondEta.property.eval {
      rule := .eta
      selected := bindingSelected .eta
      declared := binding.declared .eta
      conclusion_read := implicationRead (.lam secondBody) g secondLambdaRead secondRead
      step := .eta }
  obtain ⟨backTree⟩ := HOLKernelCongruenceReadback.symmetry_admitted signature abbreviation profile distinct dictionary parameters rules names
    _ antecedent _ _ typeSorted antecedentSorted firstLambdaSorted firstSorted firstEta antecedentMeaning (.lam firstBody) f
    antecedentRead typeRead firstLambdaRead firstRead ruleAt bindingAt (selected .symmetry) firstEtaTree
  obtain ⟨joinedTree⟩ := HOLKernelCongruenceReadback.transitivity_admitted signature abbreviation profile distinct dictionary parameters rules names
    antecedent _ _ _ _ antecedentSorted typeSorted firstSorted firstLambdaSorted secondLambdaSorted firstBack abstraction antecedentMeaning f (.lam firstBody) (.lam secondBody)
    antecedentRead typeRead firstRead firstLambdaRead secondLambdaRead ruleAt bindingAt (selected .transitivity) backTree abstractionTree
  have finalTree := HOLKernelCongruenceReadback.transitivity_admitted signature abbreviation profile distinct dictionary parameters rules names
    antecedent _ _ _ _ antecedentSorted typeSorted firstSorted secondLambdaSorted secondSorted joined secondEta antecedentMeaning f (.lam secondBody) g
    antecedentRead typeRead firstRead secondLambdaRead secondRead ruleAt bindingAt (selected .transitivity) joinedTree secondEtaTree
  exact ⟨_, finalTree⟩

#print axioms functionExtensionality_admitted
end Mettapedia.Languages.MM0.HOLKernelExtensionalityReadback
