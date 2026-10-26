import Mettapedia.Languages.MM0.HOLKernelCongruenceReadback
import Mettapedia.Languages.MM0.HOLKernelQuantifierProofs

/-!
# Admission of native quantified inference with Boolean-equivalence conversion

The actual SPEC and EXISTS producers retain admission from successfully decoded
operands and admitted premise receipts. Their stored-definition conversion from
typed Boolean equality to the maintained equivalence abbreviation is checked
in the same fresh binder frame. Name lookup, constant-dictionary freshness,
native occurrence restrictions and theorem selection stay explicit.

These interfaces cover arbitrary admitted instances, including source-derived
substitution and canonical instances promoted to retained logical assumptions.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.MM0.HOLKernelQuantifierReadback
open Mettapedia.Logic Mettapedia.Logic.HOL
open Kernel HOLKernelSyntax HOLKernelJudgment
open HOLKernelTermReadback HOLKernelJudgmentReadback HOLKernelRuleReadback HOLKernelProofReadback
open HOLKernelTypingRules (typed boolType)
open HOLKernelInferenceRules (equality)
open HOLKernelStructuralRules (CheckedProof)
open NamedElaboration (BinderNames)
universe u
variable {Const : Ty Unit → Type u} {gamma : Ctx Unit}
variable {sorts : SortSignature} {terms : TermSignature} {definitions : Definition.Signature}
variable {theorems : TheoremSignature} {context : Context}
theorem universalElimination_admitted (signature : Signature sorts terms)
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (rules : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (antecedent domain argument body result : Preterm) (boundIndex : Nat)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (domainSorted : Preterm.HasType terms context domain [] signature.ids.type)
    (bound : context[boundIndex]? = some (.bound signature.ids.object))
    (argumentSorted : Preterm.HasType terms context argument [] signature.ids.object)
    (bodySorted : Preterm.HasType terms context body [] signature.ids.object)
    (resultSorted : Preterm.HasType terms context result [] signature.ids.object)
    (antecedentIndependent : ¬ Preterm.HasVar context boundIndex antecedent)
    (domainIndependent : ¬ Preterm.HasVar context boundIndex domain)
    (argumentTyping : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := []) (typed signature.symbol antecedent argument domain))
    (resultTyping : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := []) (typed signature.symbol antecedent result (boolType signature.symbol)))
    (substitutionEquation : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := [])
      (entails signature.symbol (conjunction signature.symbol antecedent
        (holds signature.symbol (equality signature.symbol domain (.var boundIndex) argument)))
        (holds signature.symbol (equality signature.symbol (boolType signature.symbol) body result))))
    (universal : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := [])
      (entails signature.symbol antecedent
        (holds signature.symbol (applySymbol signature.symbol .allc [.var boundIndex, domain, body]))))

    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (distinct : ∀ symbol, signature.symbol symbol ≠ abbreviation.reference)
    (dictionary : Nat → Option (NamedElaboration.SomeConst Const)) (parameters : Nat) (names : Names gamma)
    (domainType : Ty Unit) (value : Term Const gamma domainType) (predicate : Formula Const (domainType :: gamma))
    (instanceFormula : Formula Const gamma) (g : Judgment Const gamma)
    (antecedentRead : readJudgmentWith (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) signature.symbol names
      (expandEquivalence signature.symbol abbreviation.reference antecedent) = some g)
    (domainRead : readType signature.symbol (expandEquivalence signature.symbol abbreviation.reference domain) = some domainType)
    (argumentRead : HOLKernelLogicalFunctionReadback.reader profile dictionary parameters names
      (expandEquivalence signature.symbol abbreviation.reference argument) = some ⟨domainType, value⟩)
    (bodyRead : HOLKernelLogicalFunctionReadback.reader profile dictionary parameters (BinderNames.cons (type := domainType) boundIndex names)
      (expandEquivalence signature.symbol abbreviation.reference body) = some ⟨.prop, predicate⟩)
    (resultRead : HOLKernelLogicalFunctionReadback.reader profile dictionary parameters names
      (expandEquivalence signature.symbol abbreviation.reference result) = some ⟨.prop, instanceFormula⟩)
    (fresh : HOLKernelBindingInterpretation.freshName parameters names boundIndex = true)
    (dictionaryFresh : dictionary boundIndex = none)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (selected : bindingAt (rules.index .universalElimination) = some .universalElimination)
    {equationFuel universalFuel : Nat}
    (equationAdmitted : AdmittedProof abbreviation theorems context (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters)
      parameters ruleAt bindingAt equationFuel (BinderNames.cons (type := domainType) boundIndex names) substitutionEquation.val
      (.imp (.and (weaken (σ := domainType) g.formula) (.eq (.var .vz) (weaken (σ := domainType) value)))
        (.eq predicate (weaken (σ := domainType) instanceFormula))))
    (universalAdmitted : AdmittedProof abbreviation theorems context (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters)
      parameters ruleAt bindingAt universalFuel names universal.val (.imp g.formula (.all predicate))) :
    Nonempty (AdmittedProof abbreviation theorems context (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters)
      parameters ruleAt bindingAt (max universalFuel (equationFuel + 1) + 1) names
      (HOLKernelQuantifierProofs.universalElimination signature abbreviation rules antecedent domain argument body result boundIndex
        antecedentSorted domainSorted bound argumentSorted bodySorted resultSorted antecedentIndependent domainIndependent
        argumentTyping resultTyping substitutionEquation universal).val (.imp g.formula instanceFormula)) := by
  let compiled := HOLKernelQuantifierProofs.universalElimination signature abbreviation rules antecedent domain argument body result boundIndex
    antecedentSorted domainSorted bound argumentSorted bodySorted resultSorted antecedentIndependent domainIndependent
    argumentTyping resultTyping substitutionEquation universal
  let nextNames : Names (domainType :: gamma) := BinderNames.cons boundIndex names
  have absent : names.lookup? boundIndex = none := by
    simp only [HOLKernelBindingInterpretation.freshName, Bool.and_eq_true, decide_eq_true_eq] at fresh
    simpa using fresh.2
  have nextLookup : LookupPreserving dictionary (Rename.weaken (σ := domainType)) names nextNames :=
    LookupPreserving.weaken dictionary names domainType boundIndex absent dictionaryFresh
  have nextContextRead := logical_judgment_rename_of_read profile dictionary parameters names nextNames (Rename.weaken (σ := domainType))
    nextLookup _ g antecedentRead
  have nextArgumentRead := logical_reader_rename_of_read profile dictionary parameters names nextNames (Rename.weaken (σ := domainType))
    nextLookup _ value argumentRead
  have nextResultRead := logical_reader_rename_of_read profile dictionary parameters names nextNames (Rename.weaken (σ := domainType))
    nextLookup _ instanceFormula resultRead
  let extra := holds signature.symbol (equality signature.symbol domain (.var boundIndex) argument)
  let equalityContext := conjunction signature.symbol antecedent extra
  have extraSorted : Preterm.HasType terms context extra [] signature.ids.wff :=
    holds_sorted signature context (signature.application context .eqc _
      (.cons (.regular domainSorted) (.cons (.regular (Preterm.HasType.var (binder := .bound signature.ids.object) bound))
        (.cons (.regular argumentSorted) .nil))))
  have equalityContextSorted := conjunction_sorted signature context antecedentSorted extraSorted
  let converted := HOLKernelBooleanEquality.contractProof signature abbreviation equalityContext body result equalityContextSorted bodySorted resultSorted substitutionEquation
  have variableRead : HOLKernelLogicalFunctionReadback.reader profile dictionary parameters nextNames
      (expandEquivalence signature.symbol abbreviation.reference (.var boundIndex)) = some ⟨domainType, Term.var (.vz : Var (domainType :: gamma) domainType)⟩ := by
    simp [expandEquivalence, HOLKernelLogicalFunctionReadback.reader, readTermWith, readVariable, nextNames]
  let extraMeaning : Judgment Const (domainType :: gamma) := .assertion (.eq (.var .vz) (weaken (σ := domainType) value))
  let extendedMeaning : Judgment Const (domainType :: gamma) := .conjunction (g.rename (Rename.weaken (σ := domainType))) extraMeaning
  have extraRead : readJudgmentWith (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) signature.symbol nextNames
      (expandEquivalence signature.symbol abbreviation.reference extra) = some extraMeaning :=
    HOLKernelCongruenceReadback.equation_judgment_read signature abbreviation profile distinct dictionary parameters
      nextNames domain _ _ (.var .vz) (weaken (σ := domainType) value) domainRead variableRead nextArgumentRead
  have extendedRead : readJudgmentWith (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) signature.symbol nextNames
      (expandEquivalence signature.symbol abbreviation.reference equalityContext) = some extendedMeaning := by
    simp [equalityContext, conjunction, applySymbol, Preterm.applyArgs, expandEquivalence, distinct,
      readJudgmentWith, readHead_reference signature.symbol signature.symbol_injective, nextContextRead, extraRead, extendedMeaning]
  obtain ⟨convertedTree⟩ := HOLKernelCongruenceReadback.contractProof_admitted signature abbreviation profile distinct dictionary parameters
    nextNames equalityContext body result equalityContextSorted bodySorted resultSorted substitutionEquation extendedMeaning predicate
    (weaken (σ := domainType) instanceFormula) extendedRead bodyRead nextResultRead ruleAt bindingAt
    (by simpa only [extendedMeaning, extraMeaning, Judgment.formula, Judgment.rename_formula, weaken] using equationAdmitted)
  have resultFormula : readFormulaIn abbreviation (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) parameters names
      (holds signature.symbol result) = some instanceFormula := by
    simp [readFormulaIn, holds, applySymbol, Preterm.applyArgs, expandEquivalence, readJudgmentWith,
      readHead_reference signature.symbol signature.symbol_injective, resultRead, expect_same, Judgment.formula]
  have conclusionRead : readFormulaIn abbreviation (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) parameters names
      (entails signature.symbol antecedent (holds signature.symbol result)) = some (.imp g.formula instanceFormula) := by
    rw [HOLKernelStructuralReadback.read_entails abbreviation signature.symbol_injective (distinct .im), resultFormula]
    simp only [readFormulaIn, antecedentRead, Option.map_some]
    rfl
  exact ⟨AdmittedStep.binding compiled.property.eval {
    rule := .universalElimination
    selected := selected
    declared := rules.declared .universalElimination
    conclusion_read := conclusionRead
    step := .universalElimination (argument := value) (universalAdmitted.weakenFuel (Nat.le_max_left _ _)) fresh
      (by simp [readObjectWith, argumentRead])
      (convertedTree.weakenFuel (Nat.le_max_right _ _)) (by
        simp only [HOL.subst, Subst.single, extendedMeaning, extraMeaning, Judgment.formula, Judgment.rename_formula]
        have singleWeak {type : Ty Unit} (term : Term Const gamma type) :
            HOL.subst (Subst.single value) (weaken (σ := domainType) term) = term := instantiate_weaken _ _
        have singleRenameWeak {type : Ty Unit} (term : Term Const gamma type) :
            HOL.subst (Subst.single value) (HOL.rename (Rename.weaken (σ := domainType)) term) = term := instantiate_weaken _ _
        simp only [singleWeak, singleRenameWeak]
        rfl) }⟩

#print axioms universalElimination_admitted
theorem existentialIntroduction_admitted (signature : Signature sorts terms)
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (rules : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (antecedent domain argument body result : Preterm) (boundIndex : Nat)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (domainSorted : Preterm.HasType terms context domain [] signature.ids.type)
    (bound : context[boundIndex]? = some (.bound signature.ids.object))
    (argumentSorted : Preterm.HasType terms context argument [] signature.ids.object)
    (bodySorted : Preterm.HasType terms context body [] signature.ids.object)
    (resultSorted : Preterm.HasType terms context result [] signature.ids.object)
    (antecedentIndependent : ¬ Preterm.HasVar context boundIndex antecedent)
    (domainIndependent : ¬ Preterm.HasVar context boundIndex domain)
    (bodyTyping : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := [])
      (typed signature.symbol (conjunction signature.symbol antecedent
        (hasType signature.symbol (.var boundIndex) domain)) body (boolType signature.symbol)))
    (argumentTyping : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := []) (typed signature.symbol antecedent argument domain))
    (substitutionEquation : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := [])
      (entails signature.symbol (conjunction signature.symbol antecedent
        (holds signature.symbol (equality signature.symbol domain (.var boundIndex) argument)))
        (holds signature.symbol (equality signature.symbol (boolType signature.symbol) body result))))
    (instanceProof : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := [])
      (entails signature.symbol antecedent (holds signature.symbol result)))
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (distinct : ∀ symbol, signature.symbol symbol ≠ abbreviation.reference)
    (dictionary : Nat → Option (NamedElaboration.SomeConst Const)) (parameters : Nat) (names : Names gamma)
    (domainType : Ty Unit) (value : Term Const gamma domainType) (predicate : Formula Const (domainType :: gamma))
    (instanceFormula : Formula Const gamma) (g : Judgment Const gamma)
    (antecedentRead : readJudgmentWith (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) signature.symbol names
      (expandEquivalence signature.symbol abbreviation.reference antecedent) = some g)
    (domainRead : readType signature.symbol (expandEquivalence signature.symbol abbreviation.reference domain) = some domainType)
    (argumentRead : HOLKernelLogicalFunctionReadback.reader profile dictionary parameters names
      (expandEquivalence signature.symbol abbreviation.reference argument) = some ⟨domainType, value⟩)
    (bodyRead : HOLKernelLogicalFunctionReadback.reader profile dictionary parameters (BinderNames.cons (type := domainType) boundIndex names)
      (expandEquivalence signature.symbol abbreviation.reference body) = some ⟨.prop, predicate⟩)
    (resultRead : HOLKernelLogicalFunctionReadback.reader profile dictionary parameters names
      (expandEquivalence signature.symbol abbreviation.reference result) = some ⟨.prop, instanceFormula⟩)
    (fresh : HOLKernelBindingInterpretation.freshName parameters names boundIndex = true)
    (dictionaryFresh : dictionary boundIndex = none)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (selected : bindingAt (rules.index .existentialIntroduction) = some .existentialIntroduction)
    {equationFuel instanceFuel : Nat}
    (equationAdmitted : AdmittedProof abbreviation theorems context (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters)
      parameters ruleAt bindingAt equationFuel (BinderNames.cons (type := domainType) boundIndex names) substitutionEquation.val
      (.imp (.and (weaken (σ := domainType) g.formula) (.eq (.var .vz) (weaken (σ := domainType) value)))
        (.eq predicate (weaken (σ := domainType) instanceFormula))))
    (instanceAdmitted : AdmittedProof abbreviation theorems context (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters)
      parameters ruleAt bindingAt instanceFuel names instanceProof.val (.imp g.formula instanceFormula)) :
    Nonempty (AdmittedProof abbreviation theorems context (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters)
      parameters ruleAt bindingAt (max instanceFuel (equationFuel + 1) + 1) names
      (HOLKernelQuantifierProofs.existentialIntroduction signature abbreviation rules antecedent domain argument body result boundIndex
        antecedentSorted domainSorted bound argumentSorted bodySorted resultSorted antecedentIndependent domainIndependent
        bodyTyping argumentTyping substitutionEquation instanceProof).val (.imp g.formula (.ex predicate))) := by
  let compiled := HOLKernelQuantifierProofs.existentialIntroduction signature abbreviation rules antecedent domain argument body result boundIndex
    antecedentSorted domainSorted bound argumentSorted bodySorted resultSorted antecedentIndependent domainIndependent
    bodyTyping argumentTyping substitutionEquation instanceProof
  let nextNames : Names (domainType :: gamma) := BinderNames.cons boundIndex names
  have absent : names.lookup? boundIndex = none := by
    simp only [HOLKernelBindingInterpretation.freshName, Bool.and_eq_true, decide_eq_true_eq] at fresh
    simpa using fresh.2
  have nextLookup : LookupPreserving dictionary (Rename.weaken (σ := domainType)) names nextNames :=
    LookupPreserving.weaken dictionary names domainType boundIndex absent dictionaryFresh
  have nextContextRead := logical_judgment_rename_of_read profile dictionary parameters names nextNames (Rename.weaken (σ := domainType))
    nextLookup _ g antecedentRead
  have nextArgumentRead := logical_reader_rename_of_read profile dictionary parameters names nextNames (Rename.weaken (σ := domainType))
    nextLookup _ value argumentRead
  have nextResultRead := logical_reader_rename_of_read profile dictionary parameters names nextNames (Rename.weaken (σ := domainType))
    nextLookup _ instanceFormula resultRead
  let extra := holds signature.symbol (equality signature.symbol domain (.var boundIndex) argument)
  let equalityContext := conjunction signature.symbol antecedent extra
  have extraSorted : Preterm.HasType terms context extra [] signature.ids.wff :=
    holds_sorted signature context (signature.application context .eqc _
      (.cons (.regular domainSorted) (.cons (.regular (Preterm.HasType.var (binder := .bound signature.ids.object) bound))
        (.cons (.regular argumentSorted) .nil))))
  have equalityContextSorted := conjunction_sorted signature context antecedentSorted extraSorted
  let converted := HOLKernelBooleanEquality.contractProof signature abbreviation equalityContext body result equalityContextSorted bodySorted resultSorted substitutionEquation
  have variableRead : HOLKernelLogicalFunctionReadback.reader profile dictionary parameters nextNames
      (expandEquivalence signature.symbol abbreviation.reference (.var boundIndex)) = some ⟨domainType, Term.var (.vz : Var (domainType :: gamma) domainType)⟩ := by
    simp [expandEquivalence, HOLKernelLogicalFunctionReadback.reader, readTermWith, readVariable, nextNames]
  let extraMeaning : Judgment Const (domainType :: gamma) := .assertion (.eq (.var .vz) (weaken (σ := domainType) value))
  let extendedMeaning : Judgment Const (domainType :: gamma) := .conjunction (g.rename (Rename.weaken (σ := domainType))) extraMeaning
  have extraRead : readJudgmentWith (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) signature.symbol nextNames
      (expandEquivalence signature.symbol abbreviation.reference extra) = some extraMeaning :=
    HOLKernelCongruenceReadback.equation_judgment_read signature abbreviation profile distinct dictionary parameters
      nextNames domain _ _ (.var .vz) (weaken (σ := domainType) value) domainRead variableRead nextArgumentRead
  have extendedRead : readJudgmentWith (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) signature.symbol nextNames
      (expandEquivalence signature.symbol abbreviation.reference equalityContext) = some extendedMeaning := by
    simp [equalityContext, conjunction, applySymbol, Preterm.applyArgs, expandEquivalence, distinct,
      readJudgmentWith, readHead_reference signature.symbol signature.symbol_injective, nextContextRead, extraRead, extendedMeaning]
  obtain ⟨convertedTree⟩ := HOLKernelCongruenceReadback.contractProof_admitted signature abbreviation profile distinct dictionary parameters
    nextNames equalityContext body result equalityContextSorted bodySorted resultSorted substitutionEquation extendedMeaning predicate
    (weaken (σ := domainType) instanceFormula) extendedRead bodyRead nextResultRead ruleAt bindingAt
    (by simpa only [extendedMeaning, extraMeaning, Judgment.formula, Judgment.rename_formula, weaken] using equationAdmitted)
  have beyond : parameters ≤ boundIndex := by
    have found := fresh
    simp only [HOLKernelBindingInterpretation.freshName, Bool.and_eq_true, decide_eq_true_eq] at found
    exact found.1
  have existentialRead : HOLKernelLogicalFunctionReadback.reader profile dictionary parameters names
      (expandEquivalence signature.symbol abbreviation.reference (applySymbol signature.symbol .exc [.var boundIndex, domain, body])) =
      some ⟨.prop, Term.ex predicate⟩ := by
    simp only [applySymbol, Preterm.applyArgs, expandEquivalence, if_neg (distinct .exc)]
    exact readTermWith_existential (HOLKernelLogicalFunctionReadback.atoms profile) signature.symbol signature.symbol_injective dictionary parameters
      names _ _ domainType boundIndex predicate beyond domainRead bodyRead
  simp only [applySymbol, Preterm.applyArgs, expandEquivalence] at existentialRead
  have resultFormula : readFormulaIn abbreviation (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) parameters names
      (holds signature.symbol (applySymbol signature.symbol .exc [.var boundIndex, domain, body])) = some (.ex predicate) := by
    simp [readFormulaIn, holds, applySymbol, Preterm.applyArgs, expandEquivalence, readJudgmentWith,
      readHead_reference signature.symbol signature.symbol_injective, existentialRead, expect_same, Judgment.formula]
  have conclusionRead : readFormulaIn abbreviation (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) parameters names
      (entails signature.symbol antecedent (holds signature.symbol (applySymbol signature.symbol .exc [.var boundIndex, domain, body]))) =
      some (.imp g.formula (.ex predicate)) := by
    rw [HOLKernelStructuralReadback.read_entails abbreviation signature.symbol_injective (distinct .im), resultFormula]
    simp only [readFormulaIn, antecedentRead, Option.map_some]
    rfl
  exact ⟨AdmittedStep.binding compiled.property.eval {
    rule := .existentialIntroduction
    selected := selected
    declared := rules.declared .existentialIntroduction
    conclusion_read := conclusionRead
    step := .existentialIntroduction (argument := value) fresh
      (by simp [readObjectWith, argumentRead]) (instanceAdmitted.weakenFuel (Nat.le_max_left _ _))
      (convertedTree.weakenFuel (Nat.le_max_right _ _)) (by
        simp only [HOL.subst, Subst.single, extendedMeaning, extraMeaning, Judgment.formula, Judgment.rename_formula]
        have singleWeak {type : Ty Unit} (term : Term Const gamma type) :
            HOL.subst (Subst.single value) (weaken (σ := domainType) term) = term := instantiate_weaken _ _
        have singleRenameWeak {type : Ty Unit} (term : Term Const gamma type) :
            HOL.subst (Subst.single value) (HOL.rename (Rename.weaken (σ := domainType)) term) = term := instantiate_weaken _ _
        simp only [singleWeak, singleRenameWeak]
        rfl) }⟩

#print axioms existentialIntroduction_admitted
end Mettapedia.Languages.MM0.HOLKernelQuantifierReadback
