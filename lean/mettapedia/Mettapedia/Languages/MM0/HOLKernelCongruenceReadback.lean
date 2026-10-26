import Mettapedia.Languages.MM0.HOLKernelInferenceReadback
/-!
# Admission of native HOL equality and constructor-congruence receipts

The actual native reflexivity, transitivity and application-congruence
constructors preserve independent proof-tree admission under successful
operand readings. Typing premises retain intrinsic term reconstruction.
Native definition conversions are admitted when explicit source beta
reductions justify their decoded endpoints. The same theorem-table entries,
proof children and native conversion witnesses are retained.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.MM0.HOLKernelCongruenceReadback
open Mettapedia.Logic.HOL Kernel HOLKernelSyntax HOLKernelJudgment
open HOLKernelTermReadback HOLKernelJudgmentReadback HOLKernelRuleReadback
open HOLKernelRuleInstances HOLKernelProofReadback
open HOLKernelStructuralRules (CheckedProof)
universe u
variable {Const : Ty Unit → Type u} {gamma : Ctx Unit}
variable {sorts : SortSignature} {terms : TermSignature} {definitions : Definition.Signature}
variable {theorems : TheoremSignature} {context : Context}
variable (signature : Signature sorts terms)
variable (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
variable (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
variable (distinct : ∀ symbol, signature.symbol symbol ≠ abbreviation.reference)
variable (constants : Nat → Option (NamedElaboration.SomeConst Const)) (parameters : Nat)
local notation "R" => HOLKernelLogicalFunctionReadback.reader profile constants parameters
local notation "expand" => expandEquivalence signature.symbol abbreviation.reference
include distinct

theorem typing_read (names : Names gamma) (antecedent termCode typeCode : Preterm)
    (g : Judgment Const gamma) {type : Ty Unit} (term : Term Const gamma type)
    (contextRead : readJudgmentWith R signature.symbol names (expand antecedent) = some g)
    (typeRead : readType signature.symbol (expand typeCode) = some type)
    (termRead : R names (expand termCode) = some ⟨type, term⟩) :
    readJudgmentWith R signature.symbol names
      (expand (HOLKernelTypingRules.typed signature.symbol antecedent termCode typeCode)) =
      some (.consequence g (.typing term)) := by
  simp [HOLKernelTypingRules.typed, entails, hasType, applySymbol, Preterm.applyArgs,
    expandEquivalence, distinct, readJudgmentWith, readHead_reference signature.symbol signature.symbol_injective,
    contextRead, readTypingWith, typeRead, termRead, expect_same]

theorem equation_judgment_read (names : Names gamma) (typeCode first second : Preterm)
    {type : Ty Unit} (left right : Term Const gamma type)
    (typeRead : readType signature.symbol (expand typeCode) = some type)
    (leftRead : R names (expand first) = some ⟨type, left⟩)
    (rightRead : R names (expand second) = some ⟨type, right⟩) :
    readJudgmentWith R signature.symbol names
      (expand (holds signature.symbol (HOLKernelInferenceRules.equality signature.symbol typeCode first second))) =
      some (.assertion (.eq left right)) := by
  have decoded := readTermWith_equality (HOLKernelLogicalFunctionReadback.atoms profile)
    signature.symbol signature.symbol_injective constants parameters names
    (expand typeCode) (expand first) (expand second) type left right typeRead leftRead rightRead
  simp only [applySymbol, Preterm.applyArgs] at decoded
  simp [holds, HOLKernelInferenceRules.equality, applySymbol, Preterm.applyArgs,
    expandEquivalence, distinct, readJudgmentWith,
    readHead_reference signature.symbol signature.symbol_injective, HOLKernelLogicalFunctionReadback.reader, decoded, expect_same]
theorem equation_read (names : Names gamma) (typeCode first second : Preterm)
    {type : Ty Unit} (left right : Term Const gamma type)
    (typeRead : readType signature.symbol (expand typeCode) = some type)
    (leftRead : R names (expand first) = some ⟨type, left⟩)
    (rightRead : R names (expand second) = some ⟨type, right⟩) :
    readFormulaIn abbreviation R parameters names
      (holds signature.symbol (HOLKernelInferenceRules.equality signature.symbol typeCode first second)) =
      some (.eq left right) := by
  have decoded := equation_judgment_read signature abbreviation profile distinct constants parameters
    names typeCode first second left right typeRead leftRead rightRead
  simp only [readFormulaIn, decoded, Option.map_some, Judgment.formula]


theorem typing_admitted (names : Names gamma) (antecedent termCode typeCode : Preterm)
    (g : Judgment Const gamma) {type : Ty Unit} (term : Term Const gamma type)
    (contextRead : readJudgmentWith R signature.symbol names (expand antecedent) = some g)
    (typeRead : readType signature.symbol (expand typeCode) = some type)
    (termRead : R names (expand termCode) = some ⟨type, term⟩)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (proof : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := [])
      (HOLKernelTypingRules.typed signature.symbol antecedent termCode typeCode)) :
    Nonempty (AdmittedProof abbreviation theorems context R parameters ruleAt bindingAt 1 names
      proof.val (.imp g.formula .top)) :=
  ⟨AdmittedStep.formation proof.property.eval
    (typing_read signature abbreviation profile distinct constants parameters names
      antecedent termCode typeCode g term contextRead typeRead termRead)⟩

theorem application_of_operands_admitted
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (names : Names gamma) (rule : HOLKernelInferenceRules.Rule)
    (nativeArguments : List Preterm) (arguments : InferenceArguments Const gamma rule)
    (parsed : readInferenceArguments R signature.symbol names rule (nativeArguments.map expand) = some arguments)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (selected : ruleAt (rules.index rule) = some (.inference rule))
    (nativeInstance : TheoremInstance)
    (instantiated : TheoremDecl.Instantiates terms context
      (rule.declaration signature.symbol signature.ids abbreviation.reference) nativeArguments nativeInstance)
    (children : List ProofWitness)
    (checked : ProofWitness.Checks terms definitions theorems context []
      (.theoremApp (rules.index rule) nativeArguments children) nativeInstance.conclusion)
    (fuel : Nat)
    (childrenAdmitted : AdmittedChildren (fun child formula =>
      AdmittedProof abbreviation theorems context R parameters ruleAt bindingAt fuel names child formula)
      children arguments.premises) :
    Nonempty (AdmittedProof abbreviation theorems context R parameters ruleAt bindingAt (fuel + 1) names
      (.theoremApp (rules.index rule) nativeArguments children) arguments.conclusion) :=
  ⟨AdmittedStep.application checked.eval
    (HOLKernelInferenceReadback.admittedApplicationOfOperands signature.symbol_injective abbreviation distinct
      (HOLKernelLogicalFunctionReadback.atoms profile) constants parameters rules names rule
      nativeArguments arguments parsed ruleAt selected nativeInstance instantiated) rfl childrenAdmitted⟩

theorem reflexivity_admitted
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (names : Names gamma) (antecedent typeCode termCode : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (typeSorted : Preterm.HasType terms context typeCode [] signature.ids.type)
    (termSorted : Preterm.HasType terms context termCode [] signature.ids.object)
    (premise : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := []) (HOLKernelTypingRules.typed signature.symbol antecedent termCode typeCode))
    (g : Judgment Const gamma) {type : Ty Unit} (term : Term Const gamma type)
    (contextRead : readJudgmentWith R signature.symbol names (expand antecedent) = some g)
    (typeRead : readType signature.symbol (expand typeCode) = some type)
    (termRead : R names (expand termCode) = some ⟨type, term⟩)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (selected : ruleAt (rules.index .reflexivity) = some (.inference .reflexivity)) :
    Nonempty (AdmittedProof abbreviation theorems context R parameters ruleAt bindingAt 2 names
      (HOLKernelInferenceProofs.Native.reflexivity signature rules antecedent typeCode termCode
        antecedentSorted typeSorted termSorted premise).val (.imp g.formula (.eq term term))) := by
  let compiled := HOLKernelInferenceProofs.Native.reflexivity signature rules antecedent typeCode termCode
    antecedentSorted typeSorted termSorted premise
  have checked : ProofWitness.Checks terms definitions theorems context []
      (.theoremApp (rules.index .reflexivity) [antecedent, typeCode, termCode] [premise.val])
      (entails signature.symbol antecedent (holds signature.symbol
        (HOLKernelInferenceRules.equality signature.symbol typeCode termCode termCode))) := compiled.property
  have instantiated := checked.instantiates (rules.declared .reflexivity) (.cons premise.property .nil)
  have parsed : readInferenceArguments R signature.symbol names .reflexivity
      ([antecedent, typeCode, termCode].map expand) = some (.reflexivity g.formula term) := by
    simp [readInferenceArguments, contextRead, typeRead, readObjectWith, termRead, expect_same]
  obtain ⟨formation⟩ := typing_admitted signature abbreviation profile distinct constants parameters names
    antecedent termCode typeCode g term contextRead typeRead termRead ruleAt bindingAt premise
  exact application_of_operands_admitted signature abbreviation profile distinct constants parameters rules names
    .reflexivity [antecedent, typeCode, termCode] (.reflexivity g.formula term) parsed ruleAt bindingAt selected
    _ instantiated [premise.val] checked 1 (.cons formation .nil)

theorem transitivity_admitted
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (names : Names gamma) (antecedent typeCode first middle last : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (typeSorted : Preterm.HasType terms context typeCode [] signature.ids.type)
    (firstSorted : Preterm.HasType terms context first [] signature.ids.object)
    (middleSorted : Preterm.HasType terms context middle [] signature.ids.object)
    (lastSorted : Preterm.HasType terms context last [] signature.ids.object)
    (one : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := [])
      (entails signature.symbol antecedent (holds signature.symbol (HOLKernelInferenceRules.equality signature.symbol typeCode first middle))))
    (two : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := [])
      (entails signature.symbol antecedent (holds signature.symbol (HOLKernelInferenceRules.equality signature.symbol typeCode middle last))))
    (g : Judgment Const gamma) {type : Ty Unit} (left center right : Term Const gamma type)
    (contextRead : readJudgmentWith R signature.symbol names (expand antecedent) = some g)
    (typeRead : readType signature.symbol (expand typeCode) = some type)
    (firstRead : R names (expand first) = some ⟨type, left⟩)
    (middleRead : R names (expand middle) = some ⟨type, center⟩)
    (lastRead : R names (expand last) = some ⟨type, right⟩)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (selected : ruleAt (rules.index .transitivity) = some (.inference .transitivity))
    {fuelOne fuelTwo : Nat}
    (oneAdmitted : AdmittedProof abbreviation theorems context R parameters ruleAt bindingAt fuelOne names one.val (.imp g.formula (.eq left center)))
    (twoAdmitted : AdmittedProof abbreviation theorems context R parameters ruleAt bindingAt fuelTwo names two.val (.imp g.formula (.eq center right))) :
    Nonempty (AdmittedProof abbreviation theorems context R parameters ruleAt bindingAt (max fuelOne fuelTwo + 1) names
      (HOLKernelInferenceProofs.Native.transitivity signature rules antecedent typeCode first middle last
        antecedentSorted typeSorted firstSorted middleSorted lastSorted one two).val
      (.imp g.formula (.eq left right))) := by
  let compiled := HOLKernelInferenceProofs.Native.transitivity signature rules antecedent typeCode first middle last
    antecedentSorted typeSorted firstSorted middleSorted lastSorted one two
  have checked : ProofWitness.Checks terms definitions theorems context []
      (.theoremApp (rules.index .transitivity) [antecedent, typeCode, first, middle, last] [one.val, two.val])
      (entails signature.symbol antecedent (holds signature.symbol
        (HOLKernelInferenceRules.equality signature.symbol typeCode first last))) := compiled.property
  have instantiated := checked.instantiates (rules.declared .transitivity) (.cons one.property (.cons two.property .nil))
  have parsed : readInferenceArguments R signature.symbol names .transitivity
      ([antecedent, typeCode, first, middle, last].map expand) = some (.transitivity g.formula left center right) := by
    simp [readInferenceArguments, contextRead, typeRead, readObjectWith, firstRead, middleRead, lastRead, expect_same]
  exact application_of_operands_admitted signature abbreviation profile distinct constants parameters rules names
    .transitivity _ (.transitivity g.formula left center right) parsed ruleAt bindingAt selected
    _ instantiated [one.val, two.val] checked (max fuelOne fuelTwo)
    (.cons (oneAdmitted.weakenFuel (Nat.le_max_left _ _))
      (.cons (twoAdmitted.weakenFuel (Nat.le_max_right _ _)) .nil))

theorem applicationFunction_admitted
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (names : Names gamma) (domainCode resultCode antecedent argument first second : Preterm)
    (domainSorted : Preterm.HasType terms context domainCode [] signature.ids.type)
    (resultSorted : Preterm.HasType terms context resultCode [] signature.ids.type)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (argumentSorted : Preterm.HasType terms context argument [] signature.ids.object)
    (firstSorted : Preterm.HasType terms context first [] signature.ids.object)
    (secondSorted : Preterm.HasType terms context second [] signature.ids.object)
    (functions : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := [])
      (entails signature.symbol antecedent (holds signature.symbol
        (HOLKernelInferenceRules.equality signature.symbol
          (HOLKernelTypingRules.functionType signature.symbol domainCode resultCode) first second))))
    (argumentTyping : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := []) (HOLKernelTypingRules.typed signature.symbol antecedent argument domainCode))
    (g : Judgment Const gamma) {domain result : Ty Unit}
    (a : Term Const gamma domain) (f h : Term Const gamma (domain ⇒ result))
    (contextRead : readJudgmentWith R signature.symbol names (expand antecedent) = some g)
    (domainRead : readType signature.symbol (expand domainCode) = some domain)
    (resultRead : readType signature.symbol (expand resultCode) = some result)
    (argumentRead : R names (expand argument) = some ⟨domain, a⟩)
    (firstRead : R names (expand first) = some ⟨domain ⇒ result, f⟩)
    (secondRead : R names (expand second) = some ⟨domain ⇒ result, h⟩)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (selected : ruleAt (rules.index .applicationFunction) = some (.inference .applicationFunction))
    {fuel : Nat}
    (functionsAdmitted : AdmittedProof abbreviation theorems context R parameters ruleAt bindingAt fuel names
      functions.val (.imp g.formula (.eq f h))) :
    Nonempty (AdmittedProof abbreviation theorems context R parameters ruleAt bindingAt (max fuel 1 + 1) names
      (HOLKernelInferenceProofs.Native.applicationFunction signature rules domainCode resultCode antecedent argument first second
        domainSorted resultSorted antecedentSorted argumentSorted firstSorted secondSorted functions argumentTyping).val
      (.imp g.formula (.eq (.app f a) (.app h a)))) := by
  let compiled := HOLKernelInferenceProofs.Native.applicationFunction signature rules domainCode resultCode antecedent argument first second
    domainSorted resultSorted antecedentSorted argumentSorted firstSorted secondSorted functions argumentTyping
  have checked : ProofWitness.Checks terms definitions theorems context []
      (.theoremApp (rules.index .applicationFunction) [domainCode, resultCode, antecedent, argument, first, second]
        [functions.val, argumentTyping.val])
      (entails signature.symbol antecedent (holds signature.symbol
        (HOLKernelInferenceRules.equality signature.symbol resultCode
          (applySymbol signature.symbol .app [first, argument]) (applySymbol signature.symbol .app [second, argument])))) := compiled.property
  have instantiated := checked.instantiates (rules.declared .applicationFunction)
    (.cons functions.property (.cons argumentTyping.property .nil))
  have parsed : readInferenceArguments R signature.symbol names .applicationFunction
      ([domainCode, resultCode, antecedent, argument, first, second].map expand) = some (.applicationFunction g.formula a f h) := by
    simp [readInferenceArguments, contextRead, domainRead, resultRead, readObjectWith, argumentRead, firstRead, secondRead, expect_same]
  obtain ⟨formation⟩ := typing_admitted signature abbreviation profile distinct constants parameters names
    antecedent argument domainCode g a contextRead domainRead argumentRead ruleAt bindingAt argumentTyping
  exact application_of_operands_admitted signature abbreviation profile distinct constants parameters rules names
    .applicationFunction _ (.applicationFunction g.formula a f h) parsed ruleAt bindingAt selected
    _ instantiated _ checked (max fuel 1)
    (.cons (functionsAdmitted.weakenFuel (Nat.le_max_left _ _))
      (.cons (formation.weakenFuel (Nat.le_max_right _ _)) .nil))

theorem applicationArgument_admitted
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (names : Names gamma) (domainCode resultCode antecedent first second function : Preterm)
    (domainSorted : Preterm.HasType terms context domainCode [] signature.ids.type)
    (resultSorted : Preterm.HasType terms context resultCode [] signature.ids.type)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (firstSorted : Preterm.HasType terms context first [] signature.ids.object)
    (secondSorted : Preterm.HasType terms context second [] signature.ids.object)
    (functionSorted : Preterm.HasType terms context function [] signature.ids.object)
    (functionTyping : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := []) (HOLKernelTypingRules.typed signature.symbol antecedent function
        (HOLKernelTypingRules.functionType signature.symbol domainCode resultCode)))
    (arguments : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := [])
      (entails signature.symbol antecedent (holds signature.symbol
        (HOLKernelInferenceRules.equality signature.symbol domainCode first second))))
    (g : Judgment Const gamma) {domain result : Ty Unit}
    (a b : Term Const gamma domain) (f : Term Const gamma (domain ⇒ result))
    (contextRead : readJudgmentWith R signature.symbol names (expand antecedent) = some g)
    (domainRead : readType signature.symbol (expand domainCode) = some domain)
    (resultRead : readType signature.symbol (expand resultCode) = some result)
    (firstRead : R names (expand first) = some ⟨domain, a⟩)
    (secondRead : R names (expand second) = some ⟨domain, b⟩)
    (functionRead : R names (expand function) = some ⟨domain ⇒ result, f⟩)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (selected : ruleAt (rules.index .applicationArgument) = some (.inference .applicationArgument))
    {fuel : Nat}
    (argumentsAdmitted : AdmittedProof abbreviation theorems context R parameters ruleAt bindingAt fuel names
      arguments.val (.imp g.formula (.eq a b))) :
    Nonempty (AdmittedProof abbreviation theorems context R parameters ruleAt bindingAt (max 1 fuel + 1) names
      (HOLKernelInferenceProofs.Native.applicationArgument signature rules domainCode resultCode antecedent first second function
        domainSorted resultSorted antecedentSorted firstSorted secondSorted functionSorted functionTyping arguments).val
      (.imp g.formula (.eq (.app f a) (.app f b)))) := by
  let compiled := HOLKernelInferenceProofs.Native.applicationArgument signature rules domainCode resultCode antecedent first second function
    domainSorted resultSorted antecedentSorted firstSorted secondSorted functionSorted functionTyping arguments
  have checked : ProofWitness.Checks terms definitions theorems context []
      (.theoremApp (rules.index .applicationArgument) [domainCode, resultCode, antecedent, first, second, function]
        [functionTyping.val, arguments.val])
      (entails signature.symbol antecedent (holds signature.symbol
        (HOLKernelInferenceRules.equality signature.symbol resultCode
          (applySymbol signature.symbol .app [function, first]) (applySymbol signature.symbol .app [function, second])))) := compiled.property
  have instantiated := checked.instantiates (rules.declared .applicationArgument)
    (.cons functionTyping.property (.cons arguments.property .nil))
  have parsed : readInferenceArguments R signature.symbol names .applicationArgument
      ([domainCode, resultCode, antecedent, first, second, function].map expand) = some (.applicationArgument g.formula a b f) := by
    simp [readInferenceArguments, contextRead, domainRead, resultRead, readObjectWith, firstRead, secondRead, functionRead, expect_same]
  have functionTypeRead : readType signature.symbol
      (expand (HOLKernelTypingRules.functionType signature.symbol domainCode resultCode)) = some (domain ⇒ result) := by
    simp [HOLKernelTypingRules.functionType, applySymbol, Preterm.applyArgs, expandEquivalence, distinct,
      readType, readHead_reference signature.symbol signature.symbol_injective, domainRead, resultRead]
  obtain ⟨formation⟩ := typing_admitted signature abbreviation profile distinct constants parameters names
    antecedent function _ g f contextRead functionTypeRead functionRead ruleAt bindingAt functionTyping
  exact application_of_operands_admitted signature abbreviation profile distinct constants parameters rules names
    .applicationArgument _ (.applicationArgument g.formula a b f) parsed ruleAt bindingAt selected
    _ instantiated _ checked (max 1 fuel)
    (.cons (formation.weakenFuel (Nat.le_max_left _ _))
      (.cons (argumentsAdmitted.weakenFuel (Nat.le_max_right _ _)) .nil))

theorem application_read (names : Names gamma) {domain result : Ty Unit}
    (function argument : Preterm) (funTerm : Term Const gamma (domain ⇒ result)) (argTerm : Term Const gamma domain)
    (funRead : R names (expand function) = some ⟨domain ⇒ result, funTerm⟩)
    (argRead : R names (expand argument) = some ⟨domain, argTerm⟩) :
    R names (expand (applySymbol signature.symbol .app [function, argument])) = some ⟨result, .app funTerm argTerm⟩ := by
  have decoded := readTermWith_application (HOLKernelLogicalFunctionReadback.atoms profile)
    signature.symbol signature.symbol_injective constants parameters names
    (expand function) (expand argument) funTerm argTerm funRead argRead
  simpa only [HOLKernelLogicalFunctionReadback.reader, applySymbol, Preterm.applyArgs,
    expandEquivalence, if_neg (distinct .app)] using decoded

theorem application_admitted
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (names : Names gamma) (antecedent domainCode resultCode firstFunction secondFunction firstArgument secondArgument : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (domainSorted : Preterm.HasType terms context domainCode [] signature.ids.type)
    (resultSorted : Preterm.HasType terms context resultCode [] signature.ids.type)
    (firstFunctionSorted : Preterm.HasType terms context firstFunction [] signature.ids.object)
    (secondFunctionSorted : Preterm.HasType terms context secondFunction [] signature.ids.object)
    (firstArgumentSorted : Preterm.HasType terms context firstArgument [] signature.ids.object)
    (secondArgumentSorted : Preterm.HasType terms context secondArgument [] signature.ids.object)
    (functions : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := [])
      (entails signature.symbol antecedent (holds signature.symbol
        (HOLKernelInferenceRules.equality signature.symbol
          (HOLKernelTypingRules.functionType signature.symbol domainCode resultCode) firstFunction secondFunction))))
    (arguments : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := [])
      (entails signature.symbol antecedent (holds signature.symbol
        (HOLKernelInferenceRules.equality signature.symbol domainCode firstArgument secondArgument))))
    (g : Judgment Const gamma) {domain result : Ty Unit}
    (f h : Term Const gamma (domain ⇒ result)) (a b : Term Const gamma domain)
    (contextRead : readJudgmentWith R signature.symbol names (expand antecedent) = some g)
    (domainRead : readType signature.symbol (expand domainCode) = some domain)
    (resultRead : readType signature.symbol (expand resultCode) = some result)
    (firstFunctionRead : R names (expand firstFunction) = some ⟨domain ⇒ result, f⟩)
    (secondFunctionRead : R names (expand secondFunction) = some ⟨domain ⇒ result, h⟩)
    (firstArgumentRead : R names (expand firstArgument) = some ⟨domain, a⟩)
    (secondArgumentRead : R names (expand secondArgument) = some ⟨domain, b⟩)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (selected : ∀ rule, ruleAt (rules.index rule) = some (.inference rule))
    {fuelFunctions fuelArguments : Nat}
    (functionsAdmitted : AdmittedProof abbreviation theorems context R parameters ruleAt bindingAt fuelFunctions names
      functions.val (.imp g.formula (.eq f h)))
    (argumentsAdmitted : AdmittedProof abbreviation theorems context R parameters ruleAt bindingAt fuelArguments names
      arguments.val (.imp g.formula (.eq a b))) :
    ∃ fuel, Nonempty (AdmittedProof abbreviation theorems context R parameters ruleAt bindingAt fuel names
      (HOLKernelCongruence.application signature rules binding antecedent domainCode resultCode
        firstFunction secondFunction firstArgument secondArgument antecedentSorted domainSorted resultSorted
        firstFunctionSorted secondFunctionSorted firstArgumentSorted secondArgumentSorted functions arguments).val
      (.imp g.formula (.eq (.app f a) (.app h b)))) := by
  unfold HOLKernelCongruence.application
  dsimp only
  let argumentTyping := HOLKernelBindingProofs.Native.equalityLeftTyping signature binding
    domainCode antecedent firstArgument secondArgument domainSorted antecedentSorted
    firstArgumentSorted secondArgumentSorted arguments
  let functionTyping := HOLKernelBindingProofs.Native.equalityRightTyping signature binding
    (HOLKernelTypingRules.functionType signature.symbol domainCode resultCode) antecedent firstFunction secondFunction
    (signature.application context .function _ (.cons (.regular domainSorted) (.cons (.regular resultSorted) .nil)))
    antecedentSorted firstFunctionSorted secondFunctionSorted functions
  let changeFunction := HOLKernelInferenceProofs.Native.applicationFunction signature rules
    domainCode resultCode antecedent firstArgument firstFunction secondFunction
    domainSorted resultSorted antecedentSorted firstArgumentSorted firstFunctionSorted secondFunctionSorted
    functions argumentTyping
  let changeArgument := HOLKernelInferenceProofs.Native.applicationArgument signature rules
    domainCode resultCode antecedent firstArgument secondArgument secondFunction
    domainSorted resultSorted antecedentSorted firstArgumentSorted secondArgumentSorted secondFunctionSorted
    functionTyping arguments
  obtain ⟨functionStep⟩ := applicationFunction_admitted signature abbreviation profile distinct constants parameters
    rules names domainCode resultCode antecedent firstArgument firstFunction secondFunction
    domainSorted resultSorted antecedentSorted firstArgumentSorted firstFunctionSorted secondFunctionSorted
    functions argumentTyping g a f h contextRead domainRead resultRead firstArgumentRead firstFunctionRead secondFunctionRead
    ruleAt bindingAt (selected .applicationFunction) functionsAdmitted
  obtain ⟨argumentStep⟩ := applicationArgument_admitted signature abbreviation profile distinct constants parameters
    rules names domainCode resultCode antecedent firstArgument secondArgument secondFunction
    domainSorted resultSorted antecedentSorted firstArgumentSorted secondArgumentSorted secondFunctionSorted
    functionTyping arguments g a b h contextRead domainRead resultRead firstArgumentRead secondArgumentRead secondFunctionRead
    ruleAt bindingAt (selected .applicationArgument) argumentsAdmitted
  have applyRead := application_read signature abbreviation profile distinct constants parameters names
    (domain := domain) (result := result)
  refine ⟨max (max fuelFunctions 1 + 1) (max 1 fuelArguments + 1) + 1, ?_⟩
  exact transitivity_admitted signature abbreviation profile distinct constants parameters rules names
    antecedent resultCode _ _ _ antecedentSorted resultSorted
    (signature.application context .app _ (.cons (.regular firstFunctionSorted) (.cons (.regular firstArgumentSorted) .nil)))
    (signature.application context .app _ (.cons (.regular secondFunctionSorted) (.cons (.regular firstArgumentSorted) .nil)))
    (signature.application context .app _ (.cons (.regular secondFunctionSorted) (.cons (.regular secondArgumentSorted) .nil)))
    changeFunction changeArgument
    g (.app f a) (.app h a) (.app h b) contextRead resultRead
    (applyRead firstFunction firstArgument f a firstFunctionRead firstArgumentRead)
    (applyRead secondFunction firstArgument h a secondFunctionRead firstArgumentRead)
    (applyRead secondFunction secondArgument h b secondFunctionRead secondArgumentRead)
    ruleAt bindingAt (selected .transitivity) functionStep argumentStep

theorem binaryApplication_admitted
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (names : Names gamma) (antecedent firstCode secondCode resultCode function first first' second second' : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (firstCodeSorted : Preterm.HasType terms context firstCode [] signature.ids.type)
    (secondCodeSorted : Preterm.HasType terms context secondCode [] signature.ids.type)
    (resultCodeSorted : Preterm.HasType terms context resultCode [] signature.ids.type)
    (functionSorted : Preterm.HasType terms context function [] signature.ids.object)
    (firstSorted : Preterm.HasType terms context first [] signature.ids.object)
    (firstSorted' : Preterm.HasType terms context first' [] signature.ids.object)
    (secondSorted : Preterm.HasType terms context second [] signature.ids.object)
    (secondSorted' : Preterm.HasType terms context second' [] signature.ids.object)
    (functionTyping : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := []) (HOLKernelTypingRules.typed signature.symbol antecedent function
        (HOLKernelTypingRules.functionType signature.symbol firstCode
          (HOLKernelTypingRules.functionType signature.symbol secondCode resultCode))))
    (firstEquality : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := [])
      (entails signature.symbol antecedent (holds signature.symbol
        (HOLKernelInferenceRules.equality signature.symbol firstCode first first'))))
    (secondEquality : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := [])
      (entails signature.symbol antecedent (holds signature.symbol
        (HOLKernelInferenceRules.equality signature.symbol secondCode second second'))))
    (g : Judgment Const gamma) {firstType secondType result : Ty Unit}
    (F : Term Const gamma (firstType ⇒ secondType ⇒ result))
    (a a' : Term Const gamma firstType) (b b' : Term Const gamma secondType)
    (contextRead : readJudgmentWith R signature.symbol names (expand antecedent) = some g)
    (firstCodeRead : readType signature.symbol (expand firstCode) = some firstType)
    (secondCodeRead : readType signature.symbol (expand secondCode) = some secondType)
    (resultCodeRead : readType signature.symbol (expand resultCode) = some result)
    (functionRead : R names (expand function) = some ⟨firstType ⇒ secondType ⇒ result, F⟩)
    (firstRead : R names (expand first) = some ⟨firstType, a⟩)
    (firstRead' : R names (expand first') = some ⟨firstType, a'⟩)
    (secondRead : R names (expand second) = some ⟨secondType, b⟩)
    (secondRead' : R names (expand second') = some ⟨secondType, b'⟩)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (selected : ∀ rule, ruleAt (rules.index rule) = some (.inference rule))
    {fuelFirst fuelSecond : Nat}
    (firstAdmitted : AdmittedProof abbreviation theorems context R parameters ruleAt bindingAt fuelFirst names
      firstEquality.val (.imp g.formula (.eq a a')))
    (secondAdmitted : AdmittedProof abbreviation theorems context R parameters ruleAt bindingAt fuelSecond names
      secondEquality.val (.imp g.formula (.eq b b'))) :
    ∃ fuel, Nonempty (AdmittedProof abbreviation theorems context R parameters ruleAt bindingAt fuel names
      (HOLKernelCongruence.binaryApplication signature rules binding antecedent firstCode secondCode resultCode
        function first first' second second' antecedentSorted firstCodeSorted secondCodeSorted resultCodeSorted
        functionSorted firstSorted firstSorted' secondSorted secondSorted' functionTyping firstEquality secondEquality).val
      (.imp g.formula (.eq (.app (.app F a) b) (.app (.app F a') b')))) := by
  have partialCodeSorted := signature.application context .function [secondCode, resultCode]
    (.cons (.regular secondCodeSorted) (.cons (.regular resultCodeSorted) .nil))
  have partialCodeRead : readType signature.symbol
      (expand (HOLKernelTypingRules.functionType signature.symbol secondCode resultCode)) = some (secondType ⇒ result) := by
    simp [HOLKernelTypingRules.functionType, applySymbol, Preterm.applyArgs, expandEquivalence, distinct,
      readType, readHead_reference signature.symbol signature.symbol_injective, secondCodeRead, resultCodeRead]
  let functions := HOLKernelInferenceProofs.Native.applicationArgument signature rules
    firstCode (HOLKernelTypingRules.functionType signature.symbol secondCode resultCode) antecedent first first' function
    firstCodeSorted partialCodeSorted antecedentSorted firstSorted firstSorted' functionSorted functionTyping firstEquality
  obtain ⟨functionsAdmitted⟩ := applicationArgument_admitted signature abbreviation profile distinct constants parameters
    rules names firstCode _ antecedent first first' function firstCodeSorted partialCodeSorted antecedentSorted
    firstSorted firstSorted' functionSorted functionTyping firstEquality g a a' F contextRead firstCodeRead
    partialCodeRead firstRead firstRead' functionRead ruleAt bindingAt (selected .applicationArgument) firstAdmitted
  have firstPartialSorted := signature.application context .app _
    (.cons (.regular functionSorted) (.cons (.regular firstSorted) .nil))
  have secondPartialSorted := signature.application context .app _
    (.cons (.regular functionSorted) (.cons (.regular firstSorted') .nil))
  have firstPartialRead := application_read signature abbreviation profile distinct constants parameters names
    function first F a functionRead firstRead
  have secondPartialRead := application_read signature abbreviation profile distinct constants parameters names
    function first' F a' functionRead firstRead'
  exact application_admitted signature abbreviation profile distinct constants parameters rules binding names
    antecedent secondCode resultCode _ _ second second' antecedentSorted secondCodeSorted resultCodeSorted
    firstPartialSorted secondPartialSorted secondSorted secondSorted' functions secondEquality g
    (.app F a) (.app F a') b b' contextRead secondCodeRead resultCodeRead firstPartialRead secondPartialRead
    secondRead secondRead' ruleAt bindingAt selected functionsAdmitted secondAdmitted

open ContextualTrinity BetaNormalization

theorem convertEquality_admitted
    (names : Names gamma) (antecedent typeCode first first' second second' : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (typeSorted : Preterm.HasType terms context typeCode [] signature.ids.type)
    (firstConversion : { witness : ConvWitness // ConvWitness.Checks terms definitions context
      witness first first' signature.ids.object })
    (secondConversion : { witness : ConvWitness // ConvWitness.Checks terms definitions context
      witness second second' signature.ids.object })
    (source : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := [])
      (entails signature.symbol antecedent (holds signature.symbol
        (HOLKernelInferenceRules.equality signature.symbol typeCode first second))))
    (g : Judgment Const gamma) {type : Ty Unit} (left left' right right' : Term Const gamma type)
    (contextRead : readJudgmentWith R signature.symbol names (expand antecedent) = some g)
    (typeRead : readType signature.symbol (expand typeCode) = some type)
    (firstRead : R names (expand first') = some ⟨type, left'⟩)
    (secondRead : R names (expand second') = some ⟨type, right'⟩)
    (leftReduces : ReducesStar left left') (rightReduces : ReducesStar right right')
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    {fuel : Nat}
    (sourceAdmitted : AdmittedProof abbreviation theorems context R parameters ruleAt bindingAt fuel names
      source.val (.imp g.formula (.eq left right))) :
    Nonempty (AdmittedProof abbreviation theorems context R parameters ruleAt bindingAt (fuel + 1) names
      (HOLKernelCongruence.convertEquality signature antecedent typeCode first first' second second'
        antecedentSorted typeSorted firstConversion secondConversion source).val
      (.imp g.formula (.eq left' right'))) := by
  let compiled := HOLKernelCongruence.convertEquality signature antecedent typeCode first first' second second'
    antecedentSorted typeSorted firstConversion secondConversion source
  have targetRead : readFormulaIn abbreviation R parameters names
      (entails signature.symbol antecedent (holds signature.symbol
        (HOLKernelInferenceRules.equality signature.symbol typeCode first' second'))) =
      some (.imp g.formula (.eq left' right')) := by
    rw [HOLKernelStructuralReadback.read_entails abbreviation signature.symbol_injective (distinct .im)]
    have antecedentRead : readFormulaIn abbreviation R parameters names antecedent = some g.formula := by
      simp only [readFormulaIn, contextRead, Option.map_some]
    rw [antecedentRead, equation_read signature abbreviation profile distinct constants parameters names
      typeCode first' second' left' right' typeRead firstRead secondRead]
    rfl
  have equalitySteps : ReducesStar (Term.eq left right) (.eq left' right') :=
    star_two Term.eq (fun b ⟨step⟩ => ⟨.eqLeft b step⟩)
      (fun a _ _ ⟨step⟩ => ⟨.eqRight a step⟩) leftReduces rightReduces
  have formulaSteps : ReducesStar (.imp g.formula (.eq left right)) (.imp g.formula (.eq left' right')) :=
    star_map (Term.imp g.formula) (fun ⟨step⟩ => ⟨.impRight g.formula step⟩) equalitySteps
  exact ⟨AdmittedStep.conversion compiled.property.eval targetRead sourceAdmitted
    ⟨_, ConversionTiers.star_execution formulaSteps, ⟨.done _⟩⟩⟩

#print axioms reflexivity_admitted
#print axioms transitivity_admitted
#print axioms applicationFunction_admitted
#print axioms applicationArgument_admitted
#print axioms binaryApplication_admitted
#print axioms application_admitted
#print axioms convertEquality_admitted
omit distinct in
theorem boolean_equivalence_read (names : Names gamma) (first second : Preterm)
    (left right : Formula Const gamma)
    (leftRead : R names (expand first) = some ⟨.prop, left⟩)
    (rightRead : R names (expand second) = some ⟨.prop, right⟩) :
    readFormulaIn abbreviation R parameters names
      (holds signature.symbol (HOLKernelBooleanEquality.code abbreviation first second)) = some (.eq left right) := by
  have boolRead : readType signature.symbol (applySymbol signature.symbol .bool []) = some .prop := by
    simp [applySymbol, Preterm.applyArgs, readType, readHead_reference signature.symbol signature.symbol_injective]
  have decoded := readTermWith_equality (HOLKernelLogicalFunctionReadback.atoms profile)
    signature.symbol signature.symbol_injective constants parameters names (applySymbol signature.symbol .bool [])
    (expand first) (expand second) .prop left right boolRead leftRead rightRead
  simp only [applySymbol, Preterm.applyArgs] at decoded
  simp [readFormulaIn, holds, HOLKernelBooleanEquality.code, HOLKernelBooleanEquality.expanded,
    applySymbol, Preterm.applyArgs, expandEquivalence, readJudgmentWith,
    readHead_reference signature.symbol signature.symbol_injective,
    HOLKernelLogicalFunctionReadback.reader, decoded, expect_same, Judgment.formula]

theorem expandProof_admitted (names : Names gamma) (antecedent first second : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (firstSorted : Preterm.HasType terms context first [] signature.ids.object)
    (secondSorted : Preterm.HasType terms context second [] signature.ids.object)
    (source : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := [])
      (entails signature.symbol antecedent (holds signature.symbol (HOLKernelBooleanEquality.code abbreviation first second))))
    (g : Judgment Const gamma) (p q : Formula Const gamma)
    (contextRead : readJudgmentWith R signature.symbol names (expand antecedent) = some g)
    (firstRead : R names (expand first) = some ⟨.prop, p⟩)
    (secondRead : R names (expand second) = some ⟨.prop, q⟩)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    {fuel : Nat}
    (sourceAdmitted : AdmittedProof abbreviation theorems context R parameters ruleAt bindingAt fuel names source.val
      (.imp g.formula (.eq p q))) :
    Nonempty (AdmittedProof abbreviation theorems context R parameters ruleAt bindingAt (fuel + 1) names
      (HOLKernelBooleanEquality.expandProof signature abbreviation antecedent first second
        antecedentSorted firstSorted secondSorted source).val (.imp g.formula (.eq p q))) := by
  let compiled := HOLKernelBooleanEquality.expandProof signature abbreviation antecedent first second
    antecedentSorted firstSorted secondSorted source
  have targetRead : readFormulaIn abbreviation R parameters names
      (entails signature.symbol antecedent (holds signature.symbol (HOLKernelBooleanEquality.expanded signature.symbol first second))) =
      some (.imp g.formula (.eq p q)) := by
    rw [HOLKernelStructuralReadback.read_entails abbreviation signature.symbol_injective (distinct .im)]
    have antecedentRead : readFormulaIn abbreviation R parameters names antecedent = some g.formula := by
      simp only [readFormulaIn, contextRead, Option.map_some]
    rw [antecedentRead]
    have boolRead : readType signature.symbol (expand (HOLKernelTypingRules.boolType signature.symbol)) = some .prop := by
      simp [HOLKernelTypingRules.boolType, applySymbol, Preterm.applyArgs, expandEquivalence,
        readType, readHead_reference signature.symbol signature.symbol_injective]
    have equationRead : readFormulaIn abbreviation R parameters names
        (holds signature.symbol (HOLKernelBooleanEquality.expanded signature.symbol first second)) = some (.eq p q) := by
      simpa only [HOLKernelBooleanEquality.expanded, HOLKernelInferenceRules.equality, HOLKernelTypingRules.boolType] using
        equation_read signature abbreviation profile distinct constants parameters names
          (HOLKernelTypingRules.boolType signature.symbol) first second p q boolRead firstRead secondRead
    rw [equationRead]
    rfl
  exact ⟨AdmittedStep.conversion compiled.property.eval targetRead sourceAdmitted
    ⟨_, ⟨.done _⟩, ⟨.done _⟩⟩⟩

theorem contractProof_admitted (names : Names gamma) (antecedent first second : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (firstSorted : Preterm.HasType terms context first [] signature.ids.object)
    (secondSorted : Preterm.HasType terms context second [] signature.ids.object)
    (source : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := [])
      (entails signature.symbol antecedent (holds signature.symbol (HOLKernelBooleanEquality.expanded signature.symbol first second))))
    (g : Judgment Const gamma) (p q : Formula Const gamma)
    (contextRead : readJudgmentWith R signature.symbol names (expand antecedent) = some g)
    (firstRead : R names (expand first) = some ⟨.prop, p⟩)
    (secondRead : R names (expand second) = some ⟨.prop, q⟩)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    {fuel : Nat}
    (sourceAdmitted : AdmittedProof abbreviation theorems context R parameters ruleAt bindingAt fuel names source.val
      (.imp g.formula (.eq p q))) :
    Nonempty (AdmittedProof abbreviation theorems context R parameters ruleAt bindingAt (fuel + 1) names
      (HOLKernelBooleanEquality.contractProof signature abbreviation antecedent first second
        antecedentSorted firstSorted secondSorted source).val (.imp g.formula (.eq p q))) := by
  let compiled := HOLKernelBooleanEquality.contractProof signature abbreviation antecedent first second
    antecedentSorted firstSorted secondSorted source
  have targetRead : readFormulaIn abbreviation R parameters names
      (entails signature.symbol antecedent (holds signature.symbol (HOLKernelBooleanEquality.code abbreviation first second))) =
      some (.imp g.formula (.eq p q)) := by
    rw [HOLKernelStructuralReadback.read_entails abbreviation signature.symbol_injective (distinct .im)]
    have antecedentRead : readFormulaIn abbreviation R parameters names antecedent = some g.formula := by
      simp only [readFormulaIn, contextRead, Option.map_some]
    rw [antecedentRead]
    rw [boolean_equivalence_read signature abbreviation profile constants parameters names first second p q firstRead secondRead]
    rfl
  exact ⟨AdmittedStep.conversion compiled.property.eval targetRead sourceAdmitted
    ⟨_, ⟨.done _⟩, ⟨.done _⟩⟩⟩

theorem booleanEqualityElimination_admitted
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (names : Names gamma) (antecedent first second : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (firstSorted : Preterm.HasType terms context first [] signature.ids.object)
    (secondSorted : Preterm.HasType terms context second [] signature.ids.object)
    (equal : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := [])
      (entails signature.symbol antecedent (holds signature.symbol
        (HOLKernelInferenceRules.equality signature.symbol (HOLKernelTypingRules.boolType signature.symbol) first second))))
    (source : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := []) (entails signature.symbol antecedent (holds signature.symbol first)))
    (g : Judgment Const gamma) (p q : Formula Const gamma)
    (contextRead : readJudgmentWith R signature.symbol names (expand antecedent) = some g)
    (firstRead : R names (expand first) = some ⟨.prop, p⟩)
    (secondRead : R names (expand second) = some ⟨.prop, q⟩)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (selected : ruleAt (rules.index .booleanEqualityElimination) = some (.inference .booleanEqualityElimination))
    {fuelEqual fuelSource : Nat}
    (equalAdmitted : AdmittedProof abbreviation theorems context R parameters ruleAt bindingAt fuelEqual names equal.val
      (.imp g.formula (.eq p q)))
    (sourceAdmitted : AdmittedProof abbreviation theorems context R parameters ruleAt bindingAt fuelSource names source.val
      (.imp g.formula p)) :
    Nonempty (AdmittedProof abbreviation theorems context R parameters ruleAt bindingAt (max (fuelEqual + 1) fuelSource + 1) names
      (HOLKernelInferenceProofs.booleanEqualityElimination signature abbreviation rules antecedent first second
        antecedentSorted firstSorted secondSorted equal source).val (.imp g.formula q)) := by
  let contracted := HOLKernelBooleanEquality.contractProof signature abbreviation antecedent first second
    antecedentSorted firstSorted secondSorted equal
  let compiled := HOLKernelInferenceProofs.booleanEqualityElimination signature abbreviation rules antecedent first second
    antecedentSorted firstSorted secondSorted equal source
  obtain ⟨equalityTree⟩ := contractProof_admitted signature abbreviation profile distinct constants parameters names
    antecedent first second antecedentSorted firstSorted secondSorted equal g p q contextRead firstRead secondRead
    ruleAt bindingAt equalAdmitted
  have checked : ProofWitness.Checks terms definitions theorems context []
      (.theoremApp (rules.index .booleanEqualityElimination) [antecedent, first, second] [contracted.val, source.val])
      (entails signature.symbol antecedent (holds signature.symbol second)) := compiled.property
  have instantiated := checked.instantiates (rules.declared .booleanEqualityElimination) (.cons contracted.property (.cons source.property .nil))
  have parsed : readInferenceArguments R signature.symbol names .booleanEqualityElimination
      ([antecedent, first, second].map expand) = some (.booleanEqualityElimination g.formula p q) := by
    simp [readInferenceArguments, contextRead, firstRead, secondRead, expect_same]
  exact application_of_operands_admitted signature abbreviation profile distinct constants parameters rules names
    .booleanEqualityElimination _ (.booleanEqualityElimination g.formula p q) parsed ruleAt bindingAt selected
    _ instantiated _ checked (max (fuelEqual + 1) fuelSource)
    (.cons (equalityTree.weakenFuel (Nat.le_max_left _ _))
      (.cons (sourceAdmitted.weakenFuel (Nat.le_max_right _ _)) .nil))

#print axioms booleanEqualityElimination_admitted
theorem symmetry_admitted
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (names : Names gamma) (typeCode antecedent first second : Preterm)
    (typeSorted : Preterm.HasType terms context typeCode [] signature.ids.type)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (firstSorted : Preterm.HasType terms context first [] signature.ids.object)
    (secondSorted : Preterm.HasType terms context second [] signature.ids.object)
    (source : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := [])
      (entails signature.symbol antecedent (holds signature.symbol (HOLKernelInferenceRules.equality signature.symbol typeCode first second))))
    (g : Judgment Const gamma) {type : Ty Unit} (left right : Term Const gamma type)
    (contextRead : readJudgmentWith R signature.symbol names (expand antecedent) = some g)
    (typeRead : readType signature.symbol (expand typeCode) = some type)
    (firstRead : R names (expand first) = some ⟨type, left⟩)
    (secondRead : R names (expand second) = some ⟨type, right⟩)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (selected : ruleAt (rules.index .symmetry) = some (.inference .symmetry))
    {fuel : Nat}
    (sourceAdmitted : AdmittedProof abbreviation theorems context R parameters ruleAt bindingAt fuel names source.val (.imp g.formula (.eq left right))) :
    Nonempty (AdmittedProof abbreviation theorems context R parameters ruleAt bindingAt (fuel + 1) names
      (HOLKernelInferenceProofs.Native.symmetry signature rules typeCode antecedent first second typeSorted antecedentSorted
        firstSorted secondSorted source).val (.imp g.formula (.eq right left))) := by
  let compiled := HOLKernelInferenceProofs.Native.symmetry signature rules typeCode antecedent first second typeSorted antecedentSorted
    firstSorted secondSorted source
  have checked : ProofWitness.Checks terms definitions theorems context []
      (.theoremApp (rules.index .symmetry) [typeCode, antecedent, first, second] [source.val])
      (entails signature.symbol antecedent (holds signature.symbol
        (HOLKernelInferenceRules.equality signature.symbol typeCode second first))) := compiled.property
  have instantiated := checked.instantiates (rules.declared .symmetry) (.cons source.property .nil)
  have parsed : readInferenceArguments R signature.symbol names .symmetry
      ([typeCode, antecedent, first, second].map expand) = some (.symmetry g.formula left right) := by
    simp [readInferenceArguments, contextRead, typeRead, readObjectWith, firstRead, secondRead, expect_same]
  exact application_of_operands_admitted signature abbreviation profile distinct constants parameters rules names
    .symmetry _ (.symmetry g.formula left right) parsed ruleAt bindingAt selected _ instantiated _ checked fuel
    (.cons sourceAdmitted .nil)

#print axioms symmetry_admitted

section ContextualAdmission
open Mettapedia.Logic

/-- Reflexivity admission is stable under successful name-frame transport. -/
theorem reflexivity_admission_under_renaming
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (names : Names gamma) (antecedent typeCode native : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (typeSorted : Preterm.HasType terms context typeCode [] signature.ids.type)
    (nativeSorted : Preterm.HasType terms context native [] signature.ids.object)
    (typing : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems) (context := context) (hypotheses := [])
      (HOLKernelTypingRules.typed signature.symbol antecedent native typeCode))
    (g : Judgment Const gamma) {type : Ty Unit} (term : Term Const gamma type)
    (contextRead : readJudgmentWith (HOLKernelLogicalFunctionReadback.reader profile constants parameters) signature.symbol names
      (expandEquivalence signature.symbol abbreviation.reference antecedent) = some g)
    (typeRead : readType signature.symbol (expandEquivalence signature.symbol abbreviation.reference typeCode) = some type)
    (termRead : HOLKernelLogicalFunctionReadback.reader profile constants parameters names
      (expandEquivalence signature.symbol abbreviation.reference native) = some ⟨type, term⟩)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (selected : ruleAt (rules.index .reflexivity) = some (.inference .reflexivity)) :
    AdmissionUnderRenaming (context := context) abbreviation profile constants parameters ruleAt bindingAt names
      (HOLKernelInferenceProofs.Native.reflexivity signature rules antecedent typeCode native antecedentSorted typeSorted nativeSorted typing).val
      (.imp g.formula (.eq term term)) := by
  intro target rho future _ _ related
  have futureG := logical_judgment_rename_of_read profile constants parameters names future rho related
    (expandEquivalence signature.symbol abbreviation.reference antecedent) g contextRead
  have futureTerm := logical_reader_rename_of_read profile constants parameters names future rho related
    (expandEquivalence signature.symbol abbreviation.reference native) term termRead
  refine ⟨2, ?_⟩
  simpa only [HOL.rename, Judgment.rename_formula] using
    reflexivity_admitted signature abbreviation profile distinct constants parameters rules future antecedent typeCode native
      antecedentSorted typeSorted nativeSorted typing (g.rename rho) (HOL.rename rho term) futureG typeRead futureTerm ruleAt bindingAt selected

/-- Transitivity composes actual receipts while preserving contextual admission. -/
theorem transitivity_admission_under_renaming
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (names : Names gamma) (antecedent typeCode first middle last : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (typeSorted : Preterm.HasType terms context typeCode [] signature.ids.type)
    (firstSorted : Preterm.HasType terms context first [] signature.ids.object)
    (middleSorted : Preterm.HasType terms context middle [] signature.ids.object)
    (lastSorted : Preterm.HasType terms context last [] signature.ids.object)
    (one : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems) (context := context) (hypotheses := [])
      (entails signature.symbol antecedent (holds signature.symbol (HOLKernelInferenceRules.equality signature.symbol typeCode first middle))))
    (two : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems) (context := context) (hypotheses := [])
      (entails signature.symbol antecedent (holds signature.symbol (HOLKernelInferenceRules.equality signature.symbol typeCode middle last))))
    (g : Judgment Const gamma) {type : Ty Unit} (left center right : Term Const gamma type)
    (contextRead : readJudgmentWith (HOLKernelLogicalFunctionReadback.reader profile constants parameters) signature.symbol names
      (expandEquivalence signature.symbol abbreviation.reference antecedent) = some g)
    (typeRead : readType signature.symbol (expandEquivalence signature.symbol abbreviation.reference typeCode) = some type)
    (firstRead : HOLKernelLogicalFunctionReadback.reader profile constants parameters names
      (expandEquivalence signature.symbol abbreviation.reference first) = some ⟨type, left⟩)
    (middleRead : HOLKernelLogicalFunctionReadback.reader profile constants parameters names
      (expandEquivalence signature.symbol abbreviation.reference middle) = some ⟨type, center⟩)
    (lastRead : HOLKernelLogicalFunctionReadback.reader profile constants parameters names
      (expandEquivalence signature.symbol abbreviation.reference last) = some ⟨type, right⟩)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (selected : ruleAt (rules.index .transitivity) = some (.inference .transitivity))
    (oneAdmitted : AdmissionUnderRenaming (context := context) abbreviation profile constants parameters ruleAt bindingAt names one.val (.imp g.formula (.eq left center)))
    (twoAdmitted : AdmissionUnderRenaming (context := context) abbreviation profile constants parameters ruleAt bindingAt names two.val (.imp g.formula (.eq center right))) :
    AdmissionUnderRenaming (context := context) abbreviation profile constants parameters ruleAt bindingAt names
      (HOLKernelInferenceProofs.Native.transitivity signature rules antecedent typeCode first middle last
        antecedentSorted typeSorted firstSorted middleSorted lastSorted one two).val (.imp g.formula (.eq left right)) := by
  intro target rho future nodup above related
  obtain ⟨oneFuel, ⟨oneTree⟩⟩ := oneAdmitted rho future nodup above related
  obtain ⟨twoFuel, ⟨twoTree⟩⟩ := twoAdmitted rho future nodup above related
  have futureG := logical_judgment_rename_of_read profile constants parameters names future rho related
    (expandEquivalence signature.symbol abbreviation.reference antecedent) g contextRead
  have futureFirst := logical_reader_rename_of_read profile constants parameters names future rho related
    (expandEquivalence signature.symbol abbreviation.reference first) left firstRead
  have futureMiddle := logical_reader_rename_of_read profile constants parameters names future rho related
    (expandEquivalence signature.symbol abbreviation.reference middle) center middleRead
  have futureLast := logical_reader_rename_of_read profile constants parameters names future rho related
    (expandEquivalence signature.symbol abbreviation.reference last) right lastRead
  refine ⟨max oneFuel twoFuel + 1, ?_⟩
  simpa only [HOL.rename, Judgment.rename_formula] using
    transitivity_admitted signature abbreviation profile distinct constants parameters rules future antecedent typeCode first middle last
      antecedentSorted typeSorted firstSorted middleSorted lastSorted one two (g.rename rho)
      (HOL.rename rho left) (HOL.rename rho center) (HOL.rename rho right) futureG typeRead futureFirst futureMiddle futureLast
      ruleAt bindingAt selected (by simpa only [HOL.rename, Judgment.rename_formula] using oneTree)
      (by simpa only [HOL.rename, Judgment.rename_formula] using twoTree)

#print axioms reflexivity_admission_under_renaming
#print axioms transitivity_admission_under_renaming

end ContextualAdmission

omit distinct in
/-- Actual native checking supplies the instantiated schema for operand-based admission. -/
theorem checked_application_admitted
    (signature : Signature sorts terms)
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (distinct : ∀ symbol, signature.symbol symbol ≠ abbreviation.reference)
    (constants : Nat → Option (NamedElaboration.SomeConst Const)) (parameters : Nat)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (names : Names gamma) (rule : HOLKernelInferenceRules.Rule)
    (nativeArguments : List Preterm) (arguments : InferenceArguments Const gamma rule)
    (parsed : readInferenceArguments (HOLKernelLogicalFunctionReadback.reader profile constants parameters) signature.symbol names rule
      (nativeArguments.map (expandEquivalence signature.symbol abbreviation.reference)) = some arguments)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (selected : ruleAt (rules.index rule) = some (.inference rule))
    (statement : Preterm)
    (compiled : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems) (context := context) (hypotheses := []) statement)
    (children : List ProofWitness)
    (witness : compiled.val = .theoremApp (rules.index rule) nativeArguments children)
    (fuel : Nat)
    (childrenAdmitted : AdmittedChildren (fun child formula => AdmittedProof abbreviation theorems context
      (HOLKernelLogicalFunctionReadback.reader profile constants parameters) parameters ruleAt bindingAt fuel names child formula)
      children arguments.premises) :
    Nonempty (AdmittedProof abbreviation theorems context (HOLKernelLogicalFunctionReadback.reader profile constants parameters)
      parameters ruleAt bindingAt (fuel + 1) names compiled.val arguments.conclusion) := by
  have checked := compiled.property
  rw [witness] at checked ⊢
  cases checked with
  | @theoremApp _ actual _ _ native found instantiated childChecks =>
    have same := Option.some.inj (found.symm.trans (rules.declared rule))
    subst actual
    exact application_of_operands_admitted signature abbreviation profile distinct constants parameters rules names rule nativeArguments arguments parsed
      ruleAt bindingAt selected native instantiated children (.theoremApp (rules.declared rule) instantiated childChecks) fuel childrenAdmitted

#print axioms checked_application_admitted

end Mettapedia.Languages.MM0.HOLKernelCongruenceReadback
