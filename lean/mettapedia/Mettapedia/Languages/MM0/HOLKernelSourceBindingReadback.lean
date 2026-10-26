import Mettapedia.Languages.MM0.HOLKernelProofReadbackRenaming
import Mettapedia.Languages.MM0.HOLKernelAlphaReadback
/-!
# Admission of source-context binding constructions

Native rebinding is promoted through the actual projection from logical
assumptions to formation assumptions. The source assignment is read through
an explicit renaming into the reader's context. Rebinding freshness concerns
the image of those source variables; unused target names may be shadowed by
internal alpha binders without changing the receipt reading. Projection and rebinding
receipts share the same signature, native context, profile and decoded frame.
Universal introduction, abstraction congruence and existential elimination
preserve admission through their actual native binding, rebinding and equality
constructions, with witness-frame freshness and retained projection bounds explicit.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.MM0.HOLKernelSourceBindingReadback
open Mettapedia.Logic.HOL Kernel HOLKernelSyntax HOLKernelTermReadback HOLKernelTermAssignments HOLKernelJudgment
open HOLKernelRuleReadback HOLKernelJudgmentReadback HOLKernelProofReadback HOLKernelSourceBinding
open HOLKernelTypingRules (typed boolType functionType)
open HOLKernelInferenceRules (equality)
open HOLKernelStructuralRules (CheckedProof)
open NamedElaboration (BinderNames)
universe u
variable {Const : Ty Unit → Type u}
variable {sorts : SortSignature} {terms : TermSignature} {definitions : Definition.Signature}
variable {theorems : TheoremSignature} {context : Context}

theorem rebindInContext_admitted (signature : Signature sorts terms)
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : HOLKernelTypingRules.Rules theorems signature.symbol signature.ids)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (distinct : ∀ symbol, signature.symbol symbol ≠ abbreviation.reference)
    (dictionary : Nat → Option (NamedElaboration.SomeConst Const))
    (indices : ∀ {type}, Const type → Nat) (parameters : Nat)
    (lookup : ∀ {type} (symbol : Const type), dictionary (indices symbol) = some ⟨type, symbol⟩)
    (bounded : ∀ {type} (symbol : Const type), indices symbol < parameters)
    (base : Unit → Preterm) (constant : ∀ {type}, Const type → Preterm) (baseEq : base = fun _ => .var 0)
    (constantEq : ∀ {type} (symbol : Const type), constant symbol = .var (indices symbol))
    (binders temporary : Nat → Nat)
    (baseSorted : ∀ index, Preterm.HasType terms context (base index) [] signature.ids.type)
    (constantSorted : ∀ {type} (symbol : Const type), Preterm.HasType terms context (constant symbol) [] signature.ids.object)
    (bindersInjective : Function.Injective binders) (temporaryInjective : Function.Injective temporary)
    (bindersAbove : ∀ level, parameters ≤ binders level)
    (temporaryAbove : ∀ level, parameters ≤ temporary level)
    (baseIndependent : ∀ slot index, ¬ Preterm.HasVar context (binders slot) (base index))
    (temporaryIndependent : ∀ slot index, ¬ Preterm.HasVar context (temporary slot) (base index))
    {gamma : Ctx Unit} {type : Ty Unit} (source : Term Const gamma type) (assignment : Assignment gamma)
    (scope : HOLKernelStructuralRules.ProofContext terms definitions theorems context [] signature.symbol signature.ids.wff)
    (windows : RebindingWindows context signature.ids.object scope.formation binders temporary)
    (fits : source.binderDepth ≤ windows.width)
    (assignmentSorted : ∀ {type} (index : Var gamma type), Preterm.HasType terms context (assignment index) [] signature.ids.object)
    (variableTyping : ∀ {type} (index : Var gamma type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems) (context := context) (hypotheses := [])
        (typed signature.symbol scope.formation (assignment index) (encodeType signature.symbol base type)))
    (constantTyping : ∀ {type} (symbol : Const type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems) (context := context) (hypotheses := [])
        (typed signature.symbol scope.formation (constant symbol) (encodeType signature.symbol base type)))
    {delta : Ctx Unit} (rho : Rename Unit gamma delta) (names : Names delta)
    (nodup : names.toList.Nodup) (namesAbove : ∀ name ∈ names.toList, parameters ≤ name)
    (assignmentEq : ∀ {type} (index : Var gamma type), assignment index = .var (names.nameOf (rho index)))
    (sourceNames : ∀ offset < source.binderDepth, ∀ {type} (index : Var gamma type), binders (windows.sourceDepth + offset) ≠ names.nameOf (rho index))
    (targetNames : ∀ offset < source.binderDepth, ∀ {type} (index : Var gamma type), binders (windows.workDepth + offset) ≠ names.nameOf (rho index))
    (temporaryNames : ∀ offset < source.binderDepth, ∀ {type} (index : Var gamma type), temporary (windows.temporaryDepth + offset) ≠ names.nameOf (rho index))
    (logical formation : Judgment Const delta)
    (logicalRead : readJudgmentWith (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters)
      signature.symbol names (expandEquivalence signature.symbol abbreviation.reference scope.logical) = some logical)
    (formationRead : readJudgmentWith (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters)
      signature.symbol names (expandEquivalence signature.symbol abbreviation.reference scope.formation) = some formation)
    (ruleAt : Nat → Option HOLKernelRuleReadback.Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (selected : ∀ rule, ruleAt (rules.index rule) = some (.inference rule))
    (structuralSelected : ruleAt (structural.index .syl) = some (.structural .syl))
    (bindingSelected : bindingAt (binding.index .abstractionRenaming) = some .abstractionRenaming)
    {projectionFuel : Nat}
    (projectionAdmitted : AdmittedProof abbreviation theorems context
      (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) parameters ruleAt bindingAt projectionFuel names
      scope.projection.val (.imp logical.formula formation.formula)) :
    ∃ fuel, Nonempty (AdmittedProof abbreviation theorems context
      (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) parameters ruleAt bindingAt fuel names
      (rebindInContext signature profile structural typing rules binding base constant binders temporary
        baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent
        source assignment scope windows fits assignmentSorted variableTyping constantTyping).val
      (.imp logical.formula (.eq (rename rho source) (rename rho source)))) := by
  let equation := HOLKernelAlpha.rebind signature profile structural typing rules binding base constant binders temporary
    baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent source assignment
    windows.sourceDepth windows.workDepth windows.temporaryDepth scope.formation scope.formationSorted assignmentSorted
    (fun offset less => windows.sourceSlots offset (Nat.lt_of_lt_of_le less fits))
    (fun offset less => windows.workSlots offset (Nat.lt_of_lt_of_le less fits))
    (fun offset less => windows.temporarySlots offset (Nat.lt_of_lt_of_le less fits))
    (fun offset less => windows.sourceFresh offset (Nat.lt_of_lt_of_le less fits))
    (fun offset less => windows.workFresh offset (Nat.lt_of_lt_of_le less fits))
    (fun offset less => windows.temporaryFresh offset (Nat.lt_of_lt_of_le less fits))
    (fun first firstLess second secondLess => windows.sourceDisjoint first (Nat.lt_of_lt_of_le firstLess fits)
      second (Nat.lt_of_lt_of_le secondLess fits))
    (fun first firstLess second secondLess => Ne.symm (windows.workDisjoint second (Nat.lt_of_lt_of_le secondLess fits)
      first (Nat.lt_of_lt_of_le firstLess fits))) variableTyping constantTyping
  obtain ⟨fuel, ⟨equationTree⟩⟩ := HOLKernelAlphaReadback.rebind_admitted signature abbreviation profile structural typing rules binding
    distinct dictionary indices parameters lookup bounded base constant baseEq constantEq binders temporary
    baseSorted constantSorted bindersInjective temporaryInjective bindersAbove temporaryAbove baseIndependent temporaryIndependent
    source assignment windows.sourceDepth windows.workDepth windows.temporaryDepth scope.formation scope.formationSorted assignmentSorted
    _ _ _ _ _ _ _ _ variableTyping constantTyping rho names nodup namesAbove assignmentEq
    sourceNames
    targetNames
    temporaryNames
    formation formationRead ruleAt bindingAt selected bindingSelected
  have sourceRead := HOLKernelAlphaReadback.encoded_read abbreviation profile distinct dictionary indices parameters lookup bounded
    base constant baseEq constantEq rho names assignment assignmentEq binders bindersInjective bindersAbove
    source windows.sourceDepth nodup namesAbove sourceNames
  have targetRead := HOLKernelAlphaReadback.encoded_read abbreviation profile distinct dictionary indices parameters lookup bounded
    base constant baseEq constantEq rho names assignment assignmentEq binders bindersInjective bindersAbove
    source windows.workDepth nodup namesAbove targetNames
  have typeRead : readType signature.symbol
      (expandEquivalence signature.symbol abbreviation.reference (encodeType signature.symbol base type)) = some type := by
    rw [baseEq, expandEquivalence_encodeType_of_fixed signature.symbol abbreviation.reference distinct
      (fun _ : Unit => .var 0) (fun _ => by simp [expandEquivalence])]
    exact readType_encode signature.symbol signature.symbol_injective type
  have equationRead := HOLKernelCongruenceReadback.equation_read signature abbreviation profile distinct dictionary parameters
    names (encodeType signature.symbol base type) _ _ (rename rho source) (rename rho source) typeRead sourceRead targetRead
  have logicalFormula : readFormulaIn abbreviation (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters)
      parameters names scope.logical = some logical.formula := by
    simp only [readFormulaIn, logicalRead, Option.map_some]
  have formationFormula : readFormulaIn abbreviation (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters)
      parameters names scope.formation = some formation.formula := by
    simp only [readFormulaIn, formationRead, Option.map_some]
  have sourceSorted := encode_sorted signature context base constant binders baseSorted constantSorted source assignment
    windows.sourceDepth assignmentSorted (fun offset less => windows.sourceSlots offset (Nat.lt_of_lt_of_le less fits))
  have targetSorted := encode_sorted signature context base constant binders baseSorted constantSorted source assignment
    windows.workDepth assignmentSorted (fun offset less => windows.workSlots offset (Nat.lt_of_lt_of_le less fits))
  have lastSorted := HOLKernelJudgment.holds_sorted signature context (signature.application context .eqc _
    (.cons (.regular (encodeType_sorted signature context base baseSorted type))
      (.cons (.regular sourceSorted) (.cons (.regular targetSorted) .nil))))
  refine ⟨max projectionFuel fuel + 1, ?_⟩
  exact HOLKernelStructuralReadback.compose_admitted signature abbreviation (distinct .im) structural
    (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) parameters names ruleAt bindingAt structuralSelected
    scope.logical scope.formation _ scope.logicalSorted scope.formationSorted lastSorted scope.projection equation
    logical.formula formation.formula (.eq (rename rho source) (rename rho source))
    logicalFormula formationFormula equationRead projectionAdmitted equationTree

#print axioms rebindInContext_admitted
theorem weakenAssumption_admitted (signature : Signature sorts terms)
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : HOLKernelTypingRules.Rules theorems signature.symbol signature.ids)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (distinct : ∀ symbol, signature.symbol symbol ≠ abbreviation.reference)
    (dictionary : Nat → Option (NamedElaboration.SomeConst Const))
    (indices : ∀ {type}, Const type → Nat) (parameters : Nat)
    (lookup : ∀ {type} (symbol : Const type), dictionary (indices symbol) = some ⟨type, symbol⟩)
    (bounded : ∀ {type} (symbol : Const type), indices symbol < parameters)
    (base : Unit → Preterm) (constant : ∀ {type}, Const type → Preterm) (baseEq : base = fun _ => .var 0)
    (constantEq : ∀ {type} (symbol : Const type), constant symbol = .var (indices symbol))
    (binders temporary : Nat → Nat)
    (baseSorted : ∀ index, Preterm.HasType terms context (base index) [] signature.ids.type)
    (constantSorted : ∀ {type} (symbol : Const type), Preterm.HasType terms context (constant symbol) [] signature.ids.object)
    (bindersInjective : Function.Injective binders) (temporaryInjective : Function.Injective temporary)
    (bindersAbove : ∀ level, parameters ≤ binders level)
    (temporaryAbove : ∀ level, parameters ≤ temporary level)
    (baseIndependent : ∀ slot index, ¬ Preterm.HasVar context (binders slot) (base index))
    (temporaryIndependent : ∀ slot index, ¬ Preterm.HasVar context (temporary slot) (base index))
    {gamma : Ctx Unit} {domain : Ty Unit} (formula : Term Const gamma .prop) (assignment : Assignment gamma)
    (scope : HOLKernelStructuralRules.ProofContext terms definitions theorems context [] signature.symbol signature.ids.wff)
    (windows : RebindingWindows context signature.ids.object scope.formation binders temporary)
    (fits : formula.binderDepth + 1 ≤ windows.width)
    (assignmentSorted : ∀ {type} (index : Var gamma type), Preterm.HasType terms context (assignment index) [] signature.ids.object)
    (variableTyping : ∀ {type} (index : Var gamma type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems) (context := context) (hypotheses := [])
        (typed signature.symbol scope.formation (assignment index) (encodeType signature.symbol base type)))
    (constantTyping : ∀ {type} (symbol : Const type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems) (context := context) (hypotheses := [])
        (typed signature.symbol scope.formation (constant symbol) (encodeType signature.symbol base type)))
    (premise : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems) (context := context) (hypotheses := [])
      (entails signature.symbol scope.logical (holds signature.symbol
        (encodeWithAssignment signature.symbol base constant binders assignment windows.sourceDepth formula))))
    {delta : Ctx Unit} (rho : Rename Unit gamma delta) (names : Names delta)
    (nodup : names.toList.Nodup) (namesAbove : ∀ name ∈ names.toList, parameters ≤ name)
    (assignmentEq : ∀ {type} (index : Var gamma type), assignment index = .var (names.nameOf (rho index)))
    (sourceNames : ∀ offset < formula.binderDepth, binders (windows.sourceDepth + offset) ∉ names.toList)
    (targetNames : ∀ offset < formula.binderDepth, binders (windows.workDepth + 1 + offset) ∉ names.toList)
    (temporaryNames : ∀ offset < formula.binderDepth, temporary (windows.temporaryDepth + offset) ∉ names.toList)
    (logical formation : Judgment Const delta)
    (logicalRead : readJudgmentWith (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters)
      signature.symbol names (expandEquivalence signature.symbol abbreviation.reference scope.logical) = some logical)
    (formationRead : readJudgmentWith (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters)
      signature.symbol names (expandEquivalence signature.symbol abbreviation.reference scope.formation) = some formation)
    (rootTerm : Term Const delta domain)
    (rootRead : HOLKernelLogicalFunctionReadback.reader profile dictionary parameters names
      (.var (binders windows.workDepth)) = some ⟨domain, rootTerm⟩)
    (ruleAt : Nat → Option HOLKernelRuleReadback.Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (selected : ∀ rule, ruleAt (rules.index rule) = some (.inference rule))
    (structuralSelected : ∀ rule, ruleAt (structural.index rule) = some (.structural rule))
    (bindingSelected : bindingAt (binding.index .abstractionRenaming) = some .abstractionRenaming)
    {projectionFuel premiseFuel : Nat}
    (projectionAdmitted : AdmittedProof abbreviation theorems context
      (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) parameters ruleAt bindingAt projectionFuel names
      scope.projection.val (.imp logical.formula formation.formula))
    (premiseAdmitted : AdmittedProof abbreviation theorems context
      (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) parameters ruleAt bindingAt premiseFuel names
      premise.val (.imp logical.formula (rename rho formula))) :
    ∃ fuel, Nonempty (AdmittedProof abbreviation theorems context
      (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) parameters ruleAt bindingAt fuel names
      (weakenAssumption (domain := domain) signature abbreviation profile structural typing rules binding base constant binders temporary
        baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent
        formula assignment scope windows fits assignmentSorted variableTyping constantTyping premise).val
      (.imp (.and logical.formula .top) (rename rho formula))) := by
  let inner := windows.bodyWindow formula.binderDepth fits
  let equation := rebindInContext signature profile structural typing rules binding base constant binders temporary
    baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent formula assignment
    scope inner (Nat.le_refl _) assignmentSorted variableTyping constantTyping
  obtain ⟨equationFuel, ⟨equationTree⟩⟩ := rebindInContext_admitted signature abbreviation profile structural typing rules binding
    distinct dictionary indices parameters lookup bounded base constant baseEq constantEq binders temporary
    baseSorted constantSorted bindersInjective temporaryInjective bindersAbove temporaryAbove baseIndependent temporaryIndependent
    formula assignment scope inner (Nat.le_refl _) assignmentSorted variableTyping constantTyping rho names nodup namesAbove assignmentEq
    (fun offset less {_} index => BinderNames.ne_nameOf_of_not_mem names (sourceNames offset less) (rho index))
    (fun offset less {_} index => BinderNames.ne_nameOf_of_not_mem names (targetNames offset less) (rho index))
    (fun offset less {_} index => BinderNames.ne_nameOf_of_not_mem names (temporaryNames offset less) (rho index)) logical formation logicalRead formationRead ruleAt bindingAt selected
    (structuralSelected .syl) bindingSelected projectionAdmitted
  have sourceSorted := encode_sorted signature context base constant binders baseSorted constantSorted formula assignment
    inner.sourceDepth assignmentSorted inner.sourceSlots
  have childSorted := encode_sorted signature context base constant binders baseSorted constantSorted formula assignment
    inner.workDepth assignmentSorted inner.workSlots
  let carried := HOLKernelInferenceProofs.booleanEqualityElimination signature abbreviation rules scope.logical _ _ scope.logicalSorted
    sourceSorted childSorted equation premise
  have sourceRead := HOLKernelAlphaReadback.encoded_read abbreviation profile distinct dictionary indices parameters lookup bounded
    base constant baseEq constantEq rho names assignment assignmentEq binders bindersInjective bindersAbove
    formula inner.sourceDepth nodup namesAbove (fun offset less {_} index =>
      BinderNames.ne_nameOf_of_not_mem names (sourceNames offset less) (rho index))
  have childRead := HOLKernelAlphaReadback.encoded_read abbreviation profile distinct dictionary indices parameters lookup bounded
    base constant baseEq constantEq rho names assignment assignmentEq binders bindersInjective bindersAbove
    formula inner.workDepth nodup namesAbove (fun offset less {_} index =>
      BinderNames.ne_nameOf_of_not_mem names (targetNames offset less) (rho index))
  obtain ⟨carriedTree⟩ := HOLKernelCongruenceReadback.booleanEqualityElimination_admitted signature abbreviation profile distinct dictionary parameters
    rules names scope.logical _ _ scope.logicalSorted sourceSorted childSorted equation premise logical
    (rename rho formula) (rename rho formula) logicalRead sourceRead childRead ruleAt bindingAt
    (selected .booleanEqualityElimination) equationTree premiseAdmitted
  have head : context[binders windows.workDepth]? = some (.bound signature.ids.object) := by
    simpa only [Nat.add_zero] using windows.workSlots 0 (by omega)
  have headSorted : Preterm.HasType terms context (.var (binders windows.workDepth)) [] signature.ids.object :=
    .var (binder := .bound signature.ids.object) head
  let extra := HOLKernelJudgment.hasType signature.symbol (.var (binders windows.workDepth)) (encodeType signature.symbol base domain)
  have extraSorted := HOLKernelJudgment.hasType_sorted signature context headSorted (encodeType_sorted signature context base baseSorted domain)
  have typeRead : readType signature.symbol
      (expandEquivalence signature.symbol abbreviation.reference (encodeType signature.symbol base domain)) = some domain := by
    rw [baseEq, expandEquivalence_encodeType_of_fixed signature.symbol abbreviation.reference distinct
      (fun _ : Unit => .var 0) (fun _ => by simp [expandEquivalence])]
    exact readType_encode signature.symbol signature.symbol_injective domain
  have extraRead : readFormulaIn abbreviation (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters)
      parameters names extra = some .top := by
    simp [readFormulaIn, extra, HOLKernelJudgment.hasType, applySymbol, Preterm.applyArgs, expandEquivalence,
      distinct, readJudgmentWith, readHead_reference signature.symbol signature.symbol_injective,
      readTypingWith, typeRead, rootRead, expect_same, Judgment.formula]
  have logicalFormula : readFormulaIn abbreviation (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters)
      parameters names scope.logical = some logical.formula := by
    simp only [readFormulaIn, logicalRead, Option.map_some]
  have assertionRead : readFormulaIn abbreviation (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters)
      parameters names (HOLKernelJudgment.holds signature.symbol
        (encodeWithAssignment signature.symbol base constant binders assignment inner.workDepth formula)) = some (rename rho formula) := by
    simp [readFormulaIn, HOLKernelJudgment.holds, applySymbol, Preterm.applyArgs, expandEquivalence,
      readJudgmentWith, readHead_reference signature.symbol signature.symbol_injective, childRead, expect_same, Judgment.formula]
  let lifted := HOLKernelStructuralRules.weaken signature structural scope.logical extra _ scope.logicalSorted extraSorted
    (HOLKernelJudgment.holds_sorted signature context childSorted) carried
  obtain ⟨liftedTree⟩ := HOLKernelStructuralReadback.weaken_admitted signature abbreviation (distinct .im) (distinct .an)
    structural (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) parameters names ruleAt bindingAt structuralSelected
    scope.logical extra _ scope.logicalSorted extraSorted (HOLKernelJudgment.holds_sorted signature context childSorted) carried
    logical.formula .top (rename rho formula) logicalFormula extraRead assertionRead carriedTree
  have coherence := encode_rename (delta := domain :: gamma) signature.symbol base constant binders formula
    (fun {_} index => Var.vs index) (Assignment.extend (.var (binders windows.workDepth)) assignment) (windows.workDepth + 1)
  change encodeWithAssignment signature.symbol base constant binders
      (Assignment.extend (.var (binders windows.workDepth)) assignment) (windows.workDepth + 1) (weaken (σ := domain) formula) =
      encodeWithAssignment signature.symbol base constant binders assignment (windows.workDepth + 1) formula at coherence
  let claim := fun expression => HOLKernelJudgment.entails signature.symbol
    (HOLKernelJudgment.conjunction signature.symbol scope.logical extra) (HOLKernelJudgment.holds signature.symbol expression)
  change ∃ fuel, Nonempty (AdmittedProof abbreviation theorems context
    (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) parameters ruleAt bindingAt fuel names
    (Eq.mpr (congrArg (fun expression => CheckedProof (terms := terms) (definitions := definitions)
      (theorems := theorems) (context := context) (hypotheses := []) (claim expression)) coherence) lifted).val
    (.imp (.and logical.formula .top) (rename rho formula)))
  rw [HOLKernelStructuralRules.CheckedProof.val_mpr claim coherence lifted]
  exact ⟨_, ⟨liftedTree⟩⟩

#print axioms weakenAssumption_admitted
theorem universalIntroduction_admitted (signature : Signature sorts terms)
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : HOLKernelTypingRules.Rules theorems signature.symbol signature.ids)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (distinct : ∀ symbol, signature.symbol symbol ≠ abbreviation.reference)
    (dictionary : Nat → Option (NamedElaboration.SomeConst Const))
    (indices : ∀ {type}, Const type → Nat) (parameters : Nat)
    (lookup : ∀ {type} (symbol : Const type), dictionary (indices symbol) = some ⟨type, symbol⟩)
    (bounded : ∀ {type} (symbol : Const type), indices symbol < parameters)
    (base : Unit → Preterm) (constant : ∀ {type}, Const type → Preterm) (baseEq : base = fun _ => .var 0)
    (constantEq : ∀ {type} (symbol : Const type), constant symbol = .var (indices symbol))
    (binders temporary : Nat → Nat)
    (baseSorted : ∀ index, Preterm.HasType terms context (base index) [] signature.ids.type)
    (constantSorted : ∀ {type} (symbol : Const type), Preterm.HasType terms context (constant symbol) [] signature.ids.object)
    (bindersInjective : Function.Injective binders) (temporaryInjective : Function.Injective temporary)
    (bindersAbove : ∀ level, parameters ≤ binders level)
    (temporaryAbove : ∀ level, parameters ≤ temporary level)
    (baseIndependent : ∀ slot index, ¬ Preterm.HasVar context (binders slot) (base index))
    (temporaryIndependent : ∀ slot index, ¬ Preterm.HasVar context (temporary slot) (base index))
    {gamma : Ctx Unit} {domain : Ty Unit} (body : Term Const (domain :: gamma) .prop) (assignment : Assignment gamma)
    (scope : HOLKernelStructuralRules.ProofContext terms definitions theorems context [] signature.symbol signature.ids.wff)
    (windows : RebindingWindows context signature.ids.object scope.formation binders temporary)
    (fits : body.binderDepth + 1 ≤ windows.width)
    (logicalFresh : ¬ Preterm.HasVar context (binders windows.workDepth) scope.logical)
    (assignmentSorted : ∀ {type} (index : Var gamma type), Preterm.HasType terms context (assignment index) [] signature.ids.object)
    (variableTyping : ∀ {type} (index : Var gamma type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems) (context := context) (hypotheses := [])
        (typed signature.symbol scope.formation (assignment index) (encodeType signature.symbol base type)))
    (constantTyping : ∀ {type} (symbol : Const type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems) (context := context) (hypotheses := [])
        (typed signature.symbol scope.formation (constant symbol) (encodeType signature.symbol base type)))
    (bodyProof : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems) (context := context) (hypotheses := [])
      (entails signature.symbol (conjunction signature.symbol scope.logical
        (hasType signature.symbol (.var (binders windows.workDepth)) (encodeType signature.symbol base domain)))
        (holds signature.symbol (encodeWithAssignment signature.symbol base constant binders
          (Assignment.extend (.var (binders windows.workDepth)) assignment) (windows.workDepth + 1) body))))
    {delta : Ctx Unit} (rho : Rename Unit gamma delta) (names : Names delta)
    (nodup : names.toList.Nodup) (namesAbove : ∀ name ∈ names.toList, parameters ≤ name)
    (assignmentEq : ∀ {type} (index : Var gamma type), assignment index = .var (names.nameOf (rho index)))
    (sourceNames : ∀ offset < body.binderDepth + 1, binders (windows.sourceDepth + offset) ∉ names.toList)
    (targetNames : ∀ offset < body.binderDepth + 1, binders (windows.workDepth + offset) ∉ names.toList)
    (temporaryNames : ∀ offset < body.binderDepth + 1, temporary (windows.temporaryDepth + offset) ∉ names.toList)
    (logical formation : Judgment Const delta)
    (logicalRead : readJudgmentWith (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters)
      signature.symbol names (expandEquivalence signature.symbol abbreviation.reference scope.logical) = some logical)
    (formationRead : readJudgmentWith (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters)
      signature.symbol names (expandEquivalence signature.symbol abbreviation.reference scope.formation) = some formation)
    (ruleAt : Nat → Option HOLKernelRuleReadback.Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (selected : ∀ rule, ruleAt (rules.index rule) = some (.inference rule))
    (structuralSelected : ruleAt (structural.index .syl) = some (.structural .syl))
    (bindingSelected : ∀ rule, bindingAt (binding.index rule) = some rule)
    {projectionFuel bodyFuel : Nat}
    (projectionAdmitted : AdmittedProof abbreviation theorems context
      (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) parameters ruleAt bindingAt projectionFuel names
      scope.projection.val (.imp logical.formula formation.formula))
    (bodyAdmitted : AdmittedProof abbreviation theorems context
      (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) parameters ruleAt bindingAt bodyFuel
      (BinderNames.cons (type := domain) (binders windows.workDepth) names) bodyProof.val
      (.imp (.and (weaken (σ := domain) logical.formula) .top) (rename (Rename.lift rho) body))) :
    ∃ fuel, Nonempty (AdmittedProof abbreviation theorems context
      (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) parameters ruleAt bindingAt fuel names
      (universalIntroduction signature abbreviation profile structural typing rules binding base constant binders temporary
        baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent body assignment
        scope windows fits logicalFresh assignmentSorted variableTyping constantTyping bodyProof).val
      (.imp logical.formula (.all (rename (Rename.lift rho) body)))) := by
  have head : context[binders windows.workDepth]? = some (.bound signature.ids.object) := by
    simpa only [Nat.add_zero] using windows.workSlots 0 (by omega)
  have domainSorted := encodeType_sorted signature context base baseSorted domain
  have headSorted : Preterm.HasType terms context (.var (binders windows.workDepth)) [] signature.ids.object :=
    .var (binder := .bound signature.ids.object) head
  have extendedSorted : ∀ {type} (index : Var (domain :: gamma) type), Preterm.HasType terms context
      (Assignment.extend (.var (binders windows.workDepth)) assignment index) [] signature.ids.object :=
    Assignment.extend_sorted signature context _ assignment headSorted assignmentSorted
  have bodySorted := encode_sorted signature context base constant binders baseSorted constantSorted body _ (windows.workDepth + 1)
    extendedSorted (by
      intro offset smaller
      have found := windows.workSlots (offset + 1) (by omega)
      simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using found)
  let workProof := HOLKernelBindingProofs.Native.universalIntroduction signature binding scope.logical _
    (binders windows.workDepth) _ scope.logicalSorted domainSorted head bodySorted logicalFresh
    (HOLKernelTypeSupport.encodeType_independent context _ signature.symbol base (baseIndependent _) domain) bodyProof
  let equation := rebindInContext signature profile structural typing rules binding base constant binders temporary
    baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent (.all body) assignment
    scope windows fits assignmentSorted variableTyping constantTyping
  have sourceSorted := encode_sorted signature context base constant binders baseSorted constantSorted (.all body) assignment
    windows.sourceDepth assignmentSorted (fun offset smaller => windows.sourceSlots offset (Nat.lt_of_lt_of_le smaller fits))
  have workSorted := encode_sorted signature context base constant binders baseSorted constantSorted (.all body) assignment
    windows.workDepth assignmentSorted (fun offset smaller => windows.workSlots offset (Nat.lt_of_lt_of_le smaller fits))
  have sourceRead := HOLKernelAlphaReadback.encoded_read abbreviation profile distinct dictionary indices parameters lookup bounded
    base constant baseEq constantEq rho names assignment assignmentEq binders bindersInjective bindersAbove
    (.all body) windows.sourceDepth nodup namesAbove (fun offset less {_} index =>
      BinderNames.ne_nameOf_of_not_mem names (sourceNames offset less) (rho index))
  have workRead := HOLKernelAlphaReadback.encoded_read abbreviation profile distinct dictionary indices parameters lookup bounded
    base constant baseEq constantEq rho names assignment assignmentEq binders bindersInjective bindersAbove
    (.all body) windows.workDepth nodup namesAbove (fun offset less {_} index =>
      BinderNames.ne_nameOf_of_not_mem names (targetNames offset less) (rho index))
  have logicalFormula : readFormulaIn abbreviation (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters)
      parameters names scope.logical = some logical.formula := by
    simp only [readFormulaIn, logicalRead, Option.map_some]
  have assertionRead : readFormulaIn abbreviation (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters)
      parameters names (holds signature.symbol
        (encodeWithAssignment signature.symbol base constant binders assignment windows.workDepth (.all body))) =
      some (.all (rename (Rename.lift rho) body)) := by
    simp [readFormulaIn, holds, applySymbol, Preterm.applyArgs, expandEquivalence, readJudgmentWith,
      readHead_reference signature.symbol signature.symbol_injective, workRead, expect_same, Judgment.formula, Mettapedia.Logic.HOL.rename]
  have workConclusion : readFormulaIn abbreviation (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters)
      parameters names (entails signature.symbol scope.logical (holds signature.symbol
        (encodeWithAssignment signature.symbol base constant binders assignment windows.workDepth (.all body)))) =
      some (.imp logical.formula (.all (rename (Rename.lift rho) body))) := by
    rw [HOLKernelStructuralReadback.read_entails abbreviation signature.symbol_injective (distinct .im), logicalFormula, assertionRead]
    rfl
  have fresh : HOLKernelBindingInterpretation.freshName parameters names (binders windows.workDepth) = true := by
    have absent : names.lookup? (binders windows.workDepth) = none :=
      BinderNames.lookup?_none_of_not_mem names (by simpa only [Nat.add_zero] using targetNames 0 (Nat.zero_lt_succ _))
    simp [HOLKernelBindingInterpretation.freshName, bindersAbove, absent]
  let workTree : AdmittedProof abbreviation theorems context
      (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) parameters ruleAt bindingAt (bodyFuel + 1) names
      workProof.val (.imp logical.formula (.all (rename (Rename.lift rho) body))) :=
    AdmittedStep.binding workProof.property.eval {
      rule := .universalIntroduction
      selected := bindingSelected .universalIntroduction
      declared := binding.declared .universalIntroduction
      conclusion_read := workConclusion
      step := .universalIntroduction fresh bodyAdmitted }
  obtain ⟨equationFuel, ⟨equationTree⟩⟩ := rebindInContext_admitted signature abbreviation profile structural typing rules binding
    distinct dictionary indices parameters lookup bounded base constant baseEq constantEq binders temporary
    baseSorted constantSorted bindersInjective temporaryInjective bindersAbove temporaryAbove baseIndependent temporaryIndependent
    (.all body) assignment scope windows fits assignmentSorted variableTyping constantTyping rho names nodup namesAbove assignmentEq
    (fun offset less {_} index => BinderNames.ne_nameOf_of_not_mem names (sourceNames offset less) (rho index))
    (fun offset less {_} index => BinderNames.ne_nameOf_of_not_mem names (targetNames offset less) (rho index))
    (fun offset less {_} index => BinderNames.ne_nameOf_of_not_mem names (temporaryNames offset less) (rho index)) logical formation logicalRead formationRead ruleAt bindingAt selected structuralSelected
    (bindingSelected .abstractionRenaming) projectionAdmitted
  have boolRead : readType signature.symbol
      (expandEquivalence signature.symbol abbreviation.reference (boolType signature.symbol)) = some .prop := by
    simp [boolType, applySymbol, Preterm.applyArgs, expandEquivalence, readType, readHead_reference signature.symbol signature.symbol_injective]
  let reversed := HOLKernelInferenceProofs.Native.symmetry signature rules (boolType signature.symbol) scope.logical _ _
    (signature.application context .bool [] .nil) scope.logicalSorted sourceSorted workSorted equation
  obtain ⟨reversedTree⟩ := HOLKernelCongruenceReadback.symmetry_admitted signature abbreviation profile distinct dictionary parameters
    rules names (boolType signature.symbol) scope.logical _ _ (signature.application context .bool [] .nil)
    scope.logicalSorted sourceSorted workSorted equation logical (rename rho (.all body)) (rename rho (.all body))
    logicalRead boolRead sourceRead workRead ruleAt bindingAt (selected .symmetry) equationTree
  refine ⟨max (equationFuel + 1 + 1) (bodyFuel + 1) + 1, ?_⟩
  exact HOLKernelCongruenceReadback.booleanEqualityElimination_admitted signature abbreviation profile distinct dictionary parameters
    rules names scope.logical _ _ scope.logicalSorted workSorted sourceSorted reversed workProof logical
    (rename rho (.all body)) (rename rho (.all body)) logicalRead workRead sourceRead ruleAt bindingAt
    (selected .booleanEqualityElimination) reversedTree workTree

#print axioms universalIntroduction_admitted
theorem abstractionCongruence_admitted (signature : Signature sorts terms)
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : HOLKernelTypingRules.Rules theorems signature.symbol signature.ids)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (distinct : ∀ symbol, signature.symbol symbol ≠ abbreviation.reference)
    (dictionary : Nat → Option (NamedElaboration.SomeConst Const))
    (indices : ∀ {type}, Const type → Nat) (parameters : Nat)
    (lookup : ∀ {type} (symbol : Const type), dictionary (indices symbol) = some ⟨type, symbol⟩)
    (bounded : ∀ {type} (symbol : Const type), indices symbol < parameters)
    (base : Unit → Preterm) (constant : ∀ {type}, Const type → Preterm) (baseEq : base = fun _ => .var 0)
    (constantEq : ∀ {type} (symbol : Const type), constant symbol = .var (indices symbol))
    (binders temporary : Nat → Nat)
    (baseSorted : ∀ index, Preterm.HasType terms context (base index) [] signature.ids.type)
    (constantSorted : ∀ {type} (symbol : Const type), Preterm.HasType terms context (constant symbol) [] signature.ids.object)
    (bindersInjective : Function.Injective binders) (temporaryInjective : Function.Injective temporary)
    (bindersAbove : ∀ level, parameters ≤ binders level)
    (temporaryAbove : ∀ level, parameters ≤ temporary level)
    (baseIndependent : ∀ slot index, ¬ Preterm.HasVar context (binders slot) (base index))
    (temporaryIndependent : ∀ slot index, ¬ Preterm.HasVar context (temporary slot) (base index))
    {gamma : Ctx Unit} {domain result : Ty Unit} (first second : Term Const (domain :: gamma) result) (assignment : Assignment gamma)
    (scope : HOLKernelStructuralRules.ProofContext terms definitions theorems context [] signature.symbol signature.ids.wff)
    (windows : RebindingWindows context signature.ids.object scope.formation binders temporary)
    (fits : max first.binderDepth second.binderDepth + 1 ≤ windows.width)
    (logicalFresh : ¬ Preterm.HasVar context (binders windows.workDepth) scope.logical)
    (assignmentSorted : ∀ {type} (index : Var gamma type), Preterm.HasType terms context (assignment index) [] signature.ids.object)
    (variableTyping : ∀ {type} (index : Var gamma type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems) (context := context) (hypotheses := [])
        (typed signature.symbol scope.formation (assignment index) (encodeType signature.symbol base type)))
    (constantTyping : ∀ {type} (symbol : Const type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems) (context := context) (hypotheses := [])
        (typed signature.symbol scope.formation (constant symbol) (encodeType signature.symbol base type)))
    (bodyProof : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems) (context := context) (hypotheses := [])
      (entails signature.symbol (conjunction signature.symbol scope.logical
        (hasType signature.symbol (.var (binders windows.workDepth)) (encodeType signature.symbol base domain)))
        (holds signature.symbol (equality signature.symbol (encodeType signature.symbol base result)
          (encodeWithAssignment signature.symbol base constant binders
            (Assignment.extend (.var (binders windows.workDepth)) assignment) (windows.workDepth + 1) first)
          (encodeWithAssignment signature.symbol base constant binders
            (Assignment.extend (.var (binders windows.workDepth)) assignment) (windows.workDepth + 1) second)))))
    {delta : Ctx Unit} (rho : Rename Unit gamma delta) (names : Names delta)
    (nodup : names.toList.Nodup) (namesAbove : ∀ name ∈ names.toList, parameters ≤ name)
    (assignmentEq : ∀ {type} (index : Var gamma type), assignment index = .var (names.nameOf (rho index)))
    (sourceNames : ∀ offset < max first.binderDepth second.binderDepth + 1, binders (windows.sourceDepth + offset) ∉ names.toList)
    (targetNames : ∀ offset < max first.binderDepth second.binderDepth + 1, binders (windows.workDepth + offset) ∉ names.toList)
    (temporaryNames : ∀ offset < max first.binderDepth second.binderDepth + 1, temporary (windows.temporaryDepth + offset) ∉ names.toList)
    (logical formation : Judgment Const delta)
    (logicalRead : readJudgmentWith (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters)
      signature.symbol names (expandEquivalence signature.symbol abbreviation.reference scope.logical) = some logical)
    (formationRead : readJudgmentWith (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters)
      signature.symbol names (expandEquivalence signature.symbol abbreviation.reference scope.formation) = some formation)
    (ruleAt : Nat → Option HOLKernelRuleReadback.Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (selected : ∀ rule, ruleAt (rules.index rule) = some (.inference rule))
    (structuralSelected : ruleAt (structural.index .syl) = some (.structural .syl))
    (bindingSelected : ∀ rule, bindingAt (binding.index rule) = some rule)
    {projectionFuel bodyFuel : Nat}
    (projectionAdmitted : AdmittedProof abbreviation theorems context
      (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) parameters ruleAt bindingAt projectionFuel names
      scope.projection.val (.imp logical.formula formation.formula))
    (bodyAdmitted : AdmittedProof abbreviation theorems context
      (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) parameters ruleAt bindingAt bodyFuel
      (BinderNames.cons (type := domain) (binders windows.workDepth) names) bodyProof.val
      (.imp (.and (weaken (σ := domain) logical.formula) .top)
        (.eq (rename (Rename.lift rho) first) (rename (Rename.lift rho) second)))) :
    ∃ fuel, Nonempty (AdmittedProof abbreviation theorems context
      (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) parameters ruleAt bindingAt fuel names
      (abstractionCongruence signature profile structural typing rules binding base constant binders temporary
        baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent first second assignment
        scope windows fits logicalFresh assignmentSorted variableTyping constantTyping bodyProof).val
      (.imp logical.formula (.eq (.lam (rename (Rename.lift rho) first)) (.lam (rename (Rename.lift rho) second))))) := by
  have firstFits : (Term.lam first).binderDepth ≤ windows.width := by simp only [Term.binderDepth]; omega
  have secondFits : (Term.lam second).binderDepth ≤ windows.width := by simp only [Term.binderDepth]; omega
  have head : context[binders windows.workDepth]? = some (.bound signature.ids.object) := by
    simpa only [Nat.add_zero] using windows.workSlots 0 (by omega)
  have domainSorted := encodeType_sorted signature context base baseSorted domain
  have resultSorted := encodeType_sorted signature context base baseSorted result
  have functionSorted := encodeType_sorted signature context base baseSorted (.arr domain result)
  have headSorted : Preterm.HasType terms context (.var (binders windows.workDepth)) [] signature.ids.object :=
    .var (binder := .bound signature.ids.object) head
  have extendedSorted : ∀ {type} (index : Var (domain :: gamma) type), Preterm.HasType terms context
      (Assignment.extend (.var (binders windows.workDepth)) assignment index) [] signature.ids.object :=
    Assignment.extend_sorted signature context _ assignment headSorted assignmentSorted
  have bodySlots : ∀ offset < max first.binderDepth second.binderDepth,
      context[binders (windows.workDepth + 1 + offset)]? = some (.bound signature.ids.object) := by
    intro offset smaller
    have found := windows.workSlots (offset + 1) (by omega)
    simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using found
  have firstBodySorted := encode_sorted signature context base constant binders baseSorted constantSorted first _ (windows.workDepth + 1)
    extendedSorted (fun offset smaller => bodySlots offset (Nat.lt_of_lt_of_le smaller (Nat.le_max_left _ _)))
  have secondBodySorted := encode_sorted signature context base constant binders baseSorted constantSorted second _ (windows.workDepth + 1)
    extendedSorted (fun offset smaller => bodySlots offset (Nat.lt_of_lt_of_le smaller (Nat.le_max_right _ _)))
  let workProof := HOLKernelBindingProofs.Native.abstractionCongruence signature binding scope.logical _ _
    (binders windows.workDepth) _ _ scope.logicalSorted domainSorted resultSorted head firstBodySorted secondBodySorted logicalFresh
    (HOLKernelTypeSupport.encodeType_independent context _ signature.symbol base (baseIndependent _) domain)
    (HOLKernelTypeSupport.encodeType_independent context _ signature.symbol base (baseIndependent _) result) bodyProof
  let firstEquation := rebindInContext signature profile structural typing rules binding base constant binders temporary
    baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent (.lam first) assignment
    scope windows firstFits assignmentSorted variableTyping constantTyping
  let secondEquation := rebindInContext signature profile structural typing rules binding base constant binders temporary
    baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent (.lam second) assignment
    scope windows secondFits assignmentSorted variableTyping constantTyping
  have firstSourceSorted := encode_sorted signature context base constant binders baseSorted constantSorted (.lam first) assignment
    windows.sourceDepth assignmentSorted (fun offset smaller => windows.sourceSlots offset (Nat.lt_of_lt_of_le smaller firstFits))
  have firstWorkSorted := encode_sorted signature context base constant binders baseSorted constantSorted (.lam first) assignment
    windows.workDepth assignmentSorted (fun offset smaller => windows.workSlots offset (Nat.lt_of_lt_of_le smaller firstFits))
  have secondSourceSorted := encode_sorted signature context base constant binders baseSorted constantSorted (.lam second) assignment
    windows.sourceDepth assignmentSorted (fun offset smaller => windows.sourceSlots offset (Nat.lt_of_lt_of_le smaller secondFits))
  have secondWorkSorted := encode_sorted signature context base constant binders baseSorted constantSorted (.lam second) assignment
    windows.workDepth assignmentSorted (fun offset smaller => windows.workSlots offset (Nat.lt_of_lt_of_le smaller secondFits))
  let reversed := HOLKernelInferenceProofs.Native.symmetry signature rules _ scope.logical _ _
    functionSorted scope.logicalSorted secondSourceSorted secondWorkSorted secondEquation
  let middle := HOLKernelInferenceProofs.Native.transitivity signature rules scope.logical _ _ _ _ scope.logicalSorted
    functionSorted firstSourceSorted firstWorkSorted secondWorkSorted firstEquation workProof
  have firstBelow : first.binderDepth + 1 ≤ max first.binderDepth second.binderDepth + 1 := Nat.add_le_add_right (Nat.le_max_left _ _) 1
  have secondBelow : second.binderDepth + 1 ≤ max first.binderDepth second.binderDepth + 1 := Nat.add_le_add_right (Nat.le_max_right _ _) 1
  have firstSourceNames := fun offset less => sourceNames offset (Nat.lt_of_lt_of_le less firstBelow)
  have firstWorkNames := fun offset less => targetNames offset (Nat.lt_of_lt_of_le less firstBelow)
  have firstTemporaryNames := fun offset less => temporaryNames offset (Nat.lt_of_lt_of_le less firstBelow)
  have secondSourceNames := fun offset less => sourceNames offset (Nat.lt_of_lt_of_le less secondBelow)
  have secondWorkNames := fun offset less => targetNames offset (Nat.lt_of_lt_of_le less secondBelow)
  have secondTemporaryNames := fun offset less => temporaryNames offset (Nat.lt_of_lt_of_le less secondBelow)
  have firstSourceRead := HOLKernelAlphaReadback.encoded_read abbreviation profile distinct dictionary indices parameters lookup bounded
    base constant baseEq constantEq rho names assignment assignmentEq binders bindersInjective bindersAbove
    (.lam first) windows.sourceDepth nodup namesAbove (fun offset less {_} index =>
      BinderNames.ne_nameOf_of_not_mem names (firstSourceNames offset less) (rho index))
  have firstWorkRead := HOLKernelAlphaReadback.encoded_read abbreviation profile distinct dictionary indices parameters lookup bounded
    base constant baseEq constantEq rho names assignment assignmentEq binders bindersInjective bindersAbove
    (.lam first) windows.workDepth nodup namesAbove (fun offset less {_} index =>
      BinderNames.ne_nameOf_of_not_mem names (firstWorkNames offset less) (rho index))
  have secondSourceRead := HOLKernelAlphaReadback.encoded_read abbreviation profile distinct dictionary indices parameters lookup bounded
    base constant baseEq constantEq rho names assignment assignmentEq binders bindersInjective bindersAbove
    (.lam second) windows.sourceDepth nodup namesAbove (fun offset less {_} index =>
      BinderNames.ne_nameOf_of_not_mem names (secondSourceNames offset less) (rho index))
  have secondWorkRead := HOLKernelAlphaReadback.encoded_read abbreviation profile distinct dictionary indices parameters lookup bounded
    base constant baseEq constantEq rho names assignment assignmentEq binders bindersInjective bindersAbove
    (.lam second) windows.workDepth nodup namesAbove (fun offset less {_} index =>
      BinderNames.ne_nameOf_of_not_mem names (secondWorkNames offset less) (rho index))
  have typeRead : readType signature.symbol
      (expandEquivalence signature.symbol abbreviation.reference (encodeType signature.symbol base (domain ⇒ result))) = some (domain ⇒ result) := by
    rw [baseEq, expandEquivalence_encodeType_of_fixed signature.symbol abbreviation.reference distinct
      (fun _ : Unit => .var 0) (fun _ => by simp [expandEquivalence])]
    exact readType_encode signature.symbol signature.symbol_injective _
  have logicalFormula : readFormulaIn abbreviation (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters)
      parameters names scope.logical = some logical.formula := by simp only [readFormulaIn, logicalRead, Option.map_some]
  have equationRead := HOLKernelCongruenceReadback.equation_read signature abbreviation profile distinct dictionary parameters
    names (encodeType signature.symbol base (domain ⇒ result)) _ _
    (rename rho (.lam first)) (rename rho (.lam second)) typeRead firstWorkRead secondWorkRead
  have workConclusion : readFormulaIn abbreviation (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters)
      parameters names (entails signature.symbol scope.logical (holds signature.symbol
        (equality signature.symbol (encodeType signature.symbol base (domain ⇒ result))
          (encodeWithAssignment signature.symbol base constant binders assignment windows.workDepth (.lam first))
          (encodeWithAssignment signature.symbol base constant binders assignment windows.workDepth (.lam second))))) =
      some (.imp logical.formula (.eq (rename rho (.lam first)) (rename rho (.lam second)))) := by
    rw [HOLKernelStructuralReadback.read_entails abbreviation signature.symbol_injective (distinct .im), logicalFormula, equationRead]
    rfl
  have fresh : HOLKernelBindingInterpretation.freshName parameters names (binders windows.workDepth) = true := by
    have absent : names.lookup? (binders windows.workDepth) = none :=
      BinderNames.lookup?_none_of_not_mem names (by simpa only [Nat.add_zero] using targetNames 0 (Nat.zero_lt_succ _))
    simp [HOLKernelBindingInterpretation.freshName, bindersAbove, absent]
  let workTree : AdmittedProof abbreviation theorems context
      (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) parameters ruleAt bindingAt (bodyFuel + 1) names
      workProof.val (.imp logical.formula (.eq (.lam (rename (Rename.lift rho) first)) (.lam (rename (Rename.lift rho) second)))) :=
    AdmittedStep.binding workProof.property.eval {
      rule := .abstractionCongruence
      selected := bindingSelected .abstractionCongruence
      declared := binding.declared .abstractionCongruence
      conclusion_read := workConclusion
      step := .abstractionCongruence fresh bodyAdmitted }
  obtain ⟨firstFuel, ⟨firstTree⟩⟩ := rebindInContext_admitted signature abbreviation profile structural typing rules binding
    distinct dictionary indices parameters lookup bounded base constant baseEq constantEq binders temporary
    baseSorted constantSorted bindersInjective temporaryInjective bindersAbove temporaryAbove baseIndependent temporaryIndependent
    (.lam first) assignment scope windows firstFits assignmentSorted variableTyping constantTyping rho names nodup namesAbove assignmentEq
    (fun offset less {_} index => BinderNames.ne_nameOf_of_not_mem names (firstSourceNames offset less) (rho index))
    (fun offset less {_} index => BinderNames.ne_nameOf_of_not_mem names (firstWorkNames offset less) (rho index))
    (fun offset less {_} index => BinderNames.ne_nameOf_of_not_mem names (firstTemporaryNames offset less) (rho index)) logical formation logicalRead formationRead ruleAt bindingAt selected structuralSelected
    (bindingSelected .abstractionRenaming) projectionAdmitted
  obtain ⟨secondFuel, ⟨secondTree⟩⟩ := rebindInContext_admitted signature abbreviation profile structural typing rules binding
    distinct dictionary indices parameters lookup bounded base constant baseEq constantEq binders temporary
    baseSorted constantSorted bindersInjective temporaryInjective bindersAbove temporaryAbove baseIndependent temporaryIndependent
    (.lam second) assignment scope windows secondFits assignmentSorted variableTyping constantTyping rho names nodup namesAbove assignmentEq
    (fun offset less {_} index => BinderNames.ne_nameOf_of_not_mem names (secondSourceNames offset less) (rho index))
    (fun offset less {_} index => BinderNames.ne_nameOf_of_not_mem names (secondWorkNames offset less) (rho index))
    (fun offset less {_} index => BinderNames.ne_nameOf_of_not_mem names (secondTemporaryNames offset less) (rho index)) logical formation logicalRead formationRead ruleAt bindingAt selected structuralSelected
    (bindingSelected .abstractionRenaming) projectionAdmitted
  obtain ⟨reversedTree⟩ := HOLKernelCongruenceReadback.symmetry_admitted signature abbreviation profile distinct dictionary parameters
    rules names _ scope.logical _ _ functionSorted scope.logicalSorted secondSourceSorted secondWorkSorted secondEquation
    logical (rename rho (.lam second)) (rename rho (.lam second)) logicalRead typeRead secondSourceRead secondWorkRead
    ruleAt bindingAt (selected .symmetry) secondTree
  obtain ⟨middleTree⟩ := HOLKernelCongruenceReadback.transitivity_admitted signature abbreviation profile distinct dictionary parameters
    rules names scope.logical _ _ _ _ scope.logicalSorted functionSorted firstSourceSorted firstWorkSorted secondWorkSorted
    firstEquation workProof logical (rename rho (.lam first)) (rename rho (.lam first)) (rename rho (.lam second))
    logicalRead typeRead firstSourceRead firstWorkRead secondWorkRead ruleAt bindingAt (selected .transitivity) firstTree workTree
  refine ⟨max (max firstFuel (bodyFuel + 1) + 1) (secondFuel + 1) + 1, ?_⟩
  exact HOLKernelCongruenceReadback.transitivity_admitted signature abbreviation profile distinct dictionary parameters
    rules names scope.logical _ _ _ _ scope.logicalSorted functionSorted firstSourceSorted secondWorkSorted secondSourceSorted
    middle reversed logical (rename rho (.lam first)) (rename rho (.lam second)) (rename rho (.lam second))
    logicalRead typeRead firstSourceRead secondWorkRead secondSourceRead ruleAt bindingAt (selected .transitivity) middleTree reversedTree

#print axioms abstractionCongruence_admitted
theorem existentialElimination_admitted (signature : Signature sorts terms)
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : HOLKernelTypingRules.Rules theorems signature.symbol signature.ids)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (distinct : ∀ symbol, signature.symbol symbol ≠ abbreviation.reference)
    (dictionary : Nat → Option (NamedElaboration.SomeConst Const))
    (indices : ∀ {type}, Const type → Nat) (parameters : Nat)
    (lookup : ∀ {type} (symbol : Const type), dictionary (indices symbol) = some ⟨type, symbol⟩)
    (bounded : ∀ {type} (symbol : Const type), indices symbol < parameters)
    (base : Unit → Preterm) (constant : ∀ {type}, Const type → Preterm) (baseEq : base = fun _ => .var 0)
    (constantEq : ∀ {type} (symbol : Const type), constant symbol = .var (indices symbol))
    (binders temporary : Nat → Nat)
    (baseSorted : ∀ index, Preterm.HasType terms context (base index) [] signature.ids.type)
    (constantSorted : ∀ {type} (symbol : Const type), Preterm.HasType terms context (constant symbol) [] signature.ids.object)
    (bindersInjective : Function.Injective binders) (temporaryInjective : Function.Injective temporary)
    (bindersAbove : ∀ level, parameters ≤ binders level)
    (temporaryAbove : ∀ level, parameters ≤ temporary level)
    (baseIndependent : ∀ slot index, ¬ Preterm.HasVar context (binders slot) (base index))
    (temporaryIndependent : ∀ slot index, ¬ Preterm.HasVar context (temporary slot) (base index))
    {gamma : Ctx Unit} {domain : Ty Unit} (body : Term Const (domain :: gamma) .prop) (result : Term Const gamma .prop) (assignment : Assignment gamma)
    (scope : HOLKernelStructuralRules.ProofContext terms definitions theorems context [] signature.symbol signature.ids.wff)
    (windows : RebindingWindows context signature.ids.object scope.formation binders temporary)
    (fits : max (body.binderDepth + 1) (result.binderDepth + 1) ≤ windows.width)
    (logicalFresh : ¬ Preterm.HasVar context (binders windows.workDepth) scope.logical)
    (variableIndependent : ∀ {type} (index : Var gamma type),
      ¬ Preterm.HasVar context (binders windows.workDepth) (assignment index))
    (constantIndependent : ∀ {type} (symbol : Const type),
      ¬ Preterm.HasVar context (binders windows.workDepth) (constant symbol))
    (resultNamesApart : ∀ offset < result.binderDepth,
      binders windows.workDepth ≠ binders (windows.sourceDepth + offset))
    (assignmentSorted : ∀ {type} (index : Var gamma type), Preterm.HasType terms context (assignment index) [] signature.ids.object)
    (variableTyping : ∀ {type} (index : Var gamma type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems) (context := context) (hypotheses := [])
        (typed signature.symbol scope.formation (assignment index) (encodeType signature.symbol base type)))
    (constantTyping : ∀ {type} (symbol : Const type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems) (context := context) (hypotheses := [])
        (typed signature.symbol scope.formation (constant symbol) (encodeType signature.symbol base type)))
    (existsProof : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems) (context := context) (hypotheses := [])
      (entails signature.symbol scope.logical (holds signature.symbol
        (encodeWithAssignment signature.symbol base constant binders assignment windows.sourceDepth (.ex body)))))
    (bodyProof : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems) (context := context) (hypotheses := [])
      (entails signature.symbol (conjunction signature.symbol
        (conjunction signature.symbol scope.logical
          (hasType signature.symbol (.var (binders windows.workDepth)) (encodeType signature.symbol base domain)))
        (holds signature.symbol (encodeWithAssignment signature.symbol base constant binders
          (Assignment.extend (.var (binders windows.workDepth)) assignment) (windows.workDepth + 1) body)))
        (holds signature.symbol (encodeWithAssignment signature.symbol base constant binders
          (Assignment.extend (.var (binders windows.workDepth)) assignment) (windows.workDepth + 1)
          (weaken (σ := domain) result)))))
    {delta : Ctx Unit} (rho : Rename Unit gamma delta) (names : Names delta)
    (nodup : names.toList.Nodup) (namesAbove : ∀ name ∈ names.toList, parameters ≤ name)
    (assignmentEq : ∀ {type} (index : Var gamma type), assignment index = .var (names.nameOf (rho index)))
    (sourceNames : ∀ offset < max (body.binderDepth + 1) (result.binderDepth + 1), binders (windows.sourceDepth + offset) ∉ names.toList)
    (targetNames : ∀ offset < max (body.binderDepth + 1) (result.binderDepth + 1), binders (windows.workDepth + offset) ∉ names.toList)
    (temporaryNames : ∀ offset < max (body.binderDepth + 1) (result.binderDepth + 1), temporary (windows.temporaryDepth + offset) ∉ names.toList)
    (logical formation : Judgment Const delta)
    (logicalRead : readJudgmentWith (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters)
      signature.symbol names (expandEquivalence signature.symbol abbreviation.reference scope.logical) = some logical)
    (formationRead : readJudgmentWith (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters)
      signature.symbol names (expandEquivalence signature.symbol abbreviation.reference scope.formation) = some formation)
    (scopeBound : scope.VarsBelow (binders windows.workDepth))
    (ruleAt : Nat → Option HOLKernelRuleReadback.Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (selected : ∀ rule, ruleAt (rules.index rule) = some (.inference rule))
    (structuralSelected : ∀ rule, ruleAt (structural.index rule) = some (.structural rule))
    (bindingSelected : ∀ rule, bindingAt (binding.index rule) = some rule)
    {projectionFuel existentialFuel bodyFuel : Nat}
    (projectionAdmitted : AdmittedProof abbreviation theorems context
      (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) parameters ruleAt bindingAt projectionFuel names
      scope.projection.val (.imp logical.formula formation.formula))
    (existentialAdmitted : AdmittedProof abbreviation theorems context
      (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) parameters ruleAt bindingAt existentialFuel names
      existsProof.val (.imp logical.formula (.ex (rename (Rename.lift rho) body))))
    (bodyAdmitted : AdmittedProof abbreviation theorems context
      (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) parameters ruleAt bindingAt bodyFuel
      (BinderNames.cons (type := domain) (binders windows.workDepth) names) bodyProof.val
      (.imp (.and (.and (weaken (σ := domain) logical.formula) .top) (rename (Rename.lift rho) body))
        (weaken (σ := domain) (rename rho result)))) :
    ∃ fuel, Nonempty (AdmittedProof abbreviation theorems context
      (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) parameters ruleAt bindingAt fuel names
      (existentialElimination signature abbreviation profile structural typing rules binding base constant binders temporary
        baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent body result assignment
        scope windows fits logicalFresh variableIndependent constantIndependent resultNamesApart assignmentSorted variableTyping constantTyping
        existsProof bodyProof).val (.imp logical.formula (rename rho result))) := by
  have bodyFits : (Term.ex body).binderDepth ≤ windows.width := by simp only [Term.binderDepth]; omega
  have resultFits : result.binderDepth ≤ windows.width := by omega
  have head : context[binders windows.workDepth]? = some (.bound signature.ids.object) := by
    simpa only [Nat.add_zero] using windows.workSlots 0 (by omega)
  have domainSorted := encodeType_sorted signature context base baseSorted domain
  have headSorted : Preterm.HasType terms context (.var (binders windows.workDepth)) [] signature.ids.object :=
    .var (binder := .bound signature.ids.object) head
  have extendedSorted : ∀ {type} (index : Var (domain :: gamma) type), Preterm.HasType terms context
      (Assignment.extend (.var (binders windows.workDepth)) assignment index) [] signature.ids.object :=
    Assignment.extend_sorted signature context _ assignment headSorted assignmentSorted
  have bodySorted := encode_sorted signature context base constant binders baseSorted constantSorted body _ (windows.workDepth + 1)
    extendedSorted (by
      intro offset smaller
      have found := windows.workSlots (offset + 1) (by omega)
      simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using found)
  have resultSorted := encode_sorted signature context base constant binders baseSorted constantSorted result assignment
    windows.sourceDepth assignmentSorted (fun offset smaller => windows.sourceSlots offset (Nat.lt_of_lt_of_le smaller resultFits))
  have resultIndependent : ¬ Preterm.HasVar context (binders windows.workDepth)
      (encodeWithAssignment signature.symbol base constant binders assignment windows.sourceDepth result) := by
    apply encode_independent context (binders windows.workDepth) signature.symbol base constant binders
      (baseIndependent windows.workDepth) constantIndependent result assignment windows.sourceDepth variableIndependent
    intro offset smaller
    exact HOLKernelTypeSupport.boundVariable_independent context _ _ signature.ids.object
      (windows.sourceSlots offset (Nat.lt_of_lt_of_le smaller resultFits)) (resultNamesApart offset smaller)
  let formationTyping := HOLKernelTermTyping.compileWithAssignment signature structural typing base constant binders
    baseSorted constantSorted bindersInjective baseIndependent result assignment windows.sourceDepth scope.formation scope.formationSorted
    assignmentSorted (fun offset smaller => windows.sourceSlots offset (Nat.lt_of_lt_of_le smaller resultFits))
    (fun offset smaller => windows.sourceFresh offset (Nat.lt_of_lt_of_le smaller resultFits)) variableTyping constantTyping
  let resultTyping := scope.promote signature structural _
    (hasType_sorted signature context resultSorted (signature.application context .bool [] .nil)) formationTyping
  let equation := rebindInContext signature profile structural typing rules binding base constant binders temporary
    baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent (.ex body) assignment
    scope windows bodyFits assignmentSorted variableTyping constantTyping
  have sourceExistsSorted := encode_sorted signature context base constant binders baseSorted constantSorted (.ex body) assignment
    windows.sourceDepth assignmentSorted (fun offset smaller => windows.sourceSlots offset (Nat.lt_of_lt_of_le smaller bodyFits))
  have workExistsSorted := encode_sorted signature context base constant binders baseSorted constantSorted (.ex body) assignment
    windows.workDepth assignmentSorted (fun offset smaller => windows.workSlots offset (Nat.lt_of_lt_of_le smaller bodyFits))
  let workExists := HOLKernelInferenceProofs.booleanEqualityElimination signature abbreviation rules scope.logical _ _ scope.logicalSorted
    sourceExistsSorted workExistsSorted equation existsProof
  let typeExtra := hasType signature.symbol (.var (binders windows.workDepth)) (encodeType signature.symbol base domain)
  have typeExtraSorted := hasType_sorted signature context headSorted domainSorted
  let bodyExtra := holds signature.symbol (encodeWithAssignment signature.symbol base constant binders
    (Assignment.extend (.var (binders windows.workDepth)) assignment) (windows.workDepth + 1) body)
  have bodyExtraSorted := holds_sorted signature context bodySorted
  let childScope := (scope.under signature structural typeExtra typeExtraSorted).under signature structural bodyExtra bodyExtraSorted
  let childWindows := windows.bodyWindow result.binderDepth (by omega)
  let resultEquation := rebindInContext signature profile structural typing rules binding base constant binders temporary
    baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent result assignment
    childScope childWindows (Nat.le_refl _) assignmentSorted variableTyping constantTyping
  have childResultSorted := encode_sorted signature context base constant binders baseSorted constantSorted result assignment
    childWindows.workDepth assignmentSorted childWindows.workSlots
  have coherence := encode_rename (delta := domain :: gamma) signature.symbol base constant binders result
    (fun {_} index => Var.vs index) (Assignment.extend (.var (binders windows.workDepth)) assignment) (windows.workDepth + 1)
  change encodeWithAssignment signature.symbol base constant binders
      (Assignment.extend (.var (binders windows.workDepth)) assignment) (windows.workDepth + 1) (weaken (σ := domain) result) =
    encodeWithAssignment signature.symbol base constant binders assignment (windows.workDepth + 1) result at coherence
  let root := binders windows.workDepth
  let nextNames : Names (domain :: delta) := BinderNames.cons root names
  let shift : Rename Unit delta (domain :: delta) := fun index => Var.vs index
  let liftedRho : Rename Unit gamma (domain :: delta) := fun index => Var.vs (rho index)
  have weakenEq (formula : Formula Const delta) : weaken (σ := domain) formula = rename shift formula :=
    rename_ext (fun {_} index => rfl) formula
  have renamedResult : rename liftedRho result = weaken (σ := domain) (rename rho result) := by
    rw [weakenEq, rename_comp]
  have typeRead (type : Ty Unit) : readType signature.symbol
      (expandEquivalence signature.symbol abbreviation.reference (encodeType signature.symbol base type)) = some type := by
    rw [baseEq, expandEquivalence_encodeType_of_fixed signature.symbol abbreviation.reference distinct
      (fun _ : Unit => .var 0) (fun _ => by simp [expandEquivalence])]
    exact readType_encode signature.symbol signature.symbol_injective type
  have wholePositive : 0 < max (body.binderDepth + 1) (result.binderDepth + 1) := by omega
  have rootAbsent : root ∉ names.toList := by simpa only [Nat.add_zero] using targetNames 0 wholePositive
  have fresh : HOLKernelBindingInterpretation.freshName parameters names root = true := by
    simp [HOLKernelBindingInterpretation.freshName, bindersAbove, BinderNames.lookup?_none_of_not_mem names rootAbsent, root]
  have nextNodup : nextNames.toList.Nodup := List.nodup_cons.mpr ⟨rootAbsent, nodup⟩
  have nextAbove : ∀ name ∈ nextNames.toList, parameters ≤ name := by
    intro name member
    rcases List.mem_cons.mp member with rfl | member
    · exact bindersAbove _
    · exact namesAbove _ member
  have nextAssignment : ∀ {type} (index : Var gamma type), assignment index = .var (nextNames.nameOf (liftedRho index)) := by
    intro type index
    exact assignmentEq index
  have sourceResultNames : ∀ offset < result.binderDepth, binders (windows.sourceDepth + offset) ∉ nextNames.toList := by
    intro offset less member
    rcases List.mem_cons.mp member with same | member
    · exact resultNamesApart offset less same.symm
    · exact sourceNames offset (by omega) member
  have targetResultNames : ∀ offset < result.binderDepth, binders (windows.workDepth + 1 + offset) ∉ nextNames.toList := by
    intro offset less member
    rcases List.mem_cons.mp member with same | member
    · have impossible := bindersInjective same
      change windows.workDepth + 1 + offset = windows.workDepth at impossible
      omega
    · have absent := targetNames (offset + 1) (by omega)
      apply absent
      simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using member
  have temporaryResultNames : ∀ offset < result.binderDepth, temporary (windows.temporaryDepth + offset) ∉ nextNames.toList := by
    intro offset less member
    rcases List.mem_cons.mp member with same | member
    · exact windows.workDisjoint 0 (by omega) offset (by omega) (by simpa only [Nat.add_zero] using same.symm)
    · exact temporaryNames offset (by omega) member
  have bodySourceRead := HOLKernelAlphaReadback.encoded_read abbreviation profile distinct dictionary indices parameters lookup bounded
    base constant baseEq constantEq rho names assignment assignmentEq binders bindersInjective bindersAbove
    (.ex body) windows.sourceDepth nodup namesAbove (fun offset less {_} index =>
      BinderNames.ne_nameOf_of_not_mem names (sourceNames offset (by change offset < body.binderDepth + 1 at less; omega)) (rho index))
  have bodyWorkRead := HOLKernelAlphaReadback.encoded_read abbreviation profile distinct dictionary indices parameters lookup bounded
    base constant baseEq constantEq rho names assignment assignmentEq binders bindersInjective bindersAbove
    (.ex body) windows.workDepth nodup namesAbove (fun offset less {_} index =>
      BinderNames.ne_nameOf_of_not_mem names (targetNames offset (by change offset < body.binderDepth + 1 at less; omega)) (rho index))
  obtain ⟨equationFuel, ⟨equationTree⟩⟩ := rebindInContext_admitted signature abbreviation profile structural typing rules binding
    distinct dictionary indices parameters lookup bounded base constant baseEq constantEq binders temporary
    baseSorted constantSorted bindersInjective temporaryInjective bindersAbove temporaryAbove baseIndependent temporaryIndependent
    (.ex body) assignment scope windows bodyFits assignmentSorted variableTyping constantTyping rho names nodup namesAbove assignmentEq
    (fun offset less {_} index => BinderNames.ne_nameOf_of_not_mem names (sourceNames offset (by change offset < body.binderDepth + 1 at less; omega)) (rho index))
    (fun offset less {_} index => BinderNames.ne_nameOf_of_not_mem names (targetNames offset (by change offset < body.binderDepth + 1 at less; omega)) (rho index))
    (fun offset less {_} index => BinderNames.ne_nameOf_of_not_mem names (temporaryNames offset (by change offset < body.binderDepth + 1 at less; omega)) (rho index))
    logical formation logicalRead formationRead ruleAt bindingAt selected (structuralSelected .syl)
    (bindingSelected .abstractionRenaming) projectionAdmitted
  obtain ⟨existsTree⟩ := HOLKernelCongruenceReadback.booleanEqualityElimination_admitted signature abbreviation profile distinct dictionary parameters
    rules names scope.logical _ _ scope.logicalSorted sourceExistsSorted workExistsSorted equation existsProof logical
    (rename rho (.ex body)) (rename rho (.ex body)) logicalRead bodySourceRead bodyWorkRead
    ruleAt bindingAt (selected .booleanEqualityElimination) equationTree existentialAdmitted
  have nativeRoom : root ≤ context.length := Nat.le_of_lt ((List.getElem?_eq_some_iff.mp head).1)
  obtain ⟨parentProjection⟩ := projectionAdmitted.logical_weaken_of_varsBelow profile abbreviation dictionary parameters ruleAt bindingAt
    root nativeRoom scopeBound.2.2 domain root (Nat.le_refl _)
  have related : NamesRel root shift names nextNames := NamesRel.weaken names domain root (Nat.le_refl _)
  have childLogicalRead := logical_judgment_rename profile dictionary parameters root names nextNames shift related
    (expandEquivalence signature.symbol abbreviation.reference scope.logical)
    (expandEquivalence_varsBelow signature.symbol abbreviation.reference root scope.logical scopeBound.2.1)
  rw [logicalRead] at childLogicalRead
  have childFormationRead := logical_judgment_rename profile dictionary parameters root names nextNames shift related
    (expandEquivalence signature.symbol abbreviation.reference scope.formation)
    (expandEquivalence_varsBelow signature.symbol abbreviation.reference root scope.formation scopeBound.1)
  rw [formationRead] at childFormationRead
  have rootRead : HOLKernelLogicalFunctionReadback.reader profile dictionary parameters nextNames (.var root) =
      some ⟨domain, Term.var .vz⟩ := by
    simp [HOLKernelLogicalFunctionReadback.reader, readTermWith, readVariable, nextNames]
  have extraRead : readJudgmentWith (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters)
      signature.symbol nextNames (expandEquivalence signature.symbol abbreviation.reference typeExtra) =
      some (.typing (Term.var (.vz : Var (domain :: delta) domain))) := by
    simp [typeExtra, hasType, applySymbol, Preterm.applyArgs, expandEquivalence, distinct, readJudgmentWith,
      readHead_reference signature.symbol signature.symbol_injective, readTypingWith, typeRead domain, rootRead, expect_same, root]
  have bodyRead := HOLKernelAlphaReadback.encoded_body_read abbreviation profile distinct dictionary indices parameters lookup bounded
    base constant baseEq constantEq rho names assignment assignmentEq binders bindersInjective bindersAbove
    body windows.workDepth nodup namesAbove (fun offset less {_} index =>
      BinderNames.ne_nameOf_of_not_mem names (targetNames offset (by omega)) (rho index))
  have bodyExtraRead : readJudgmentWith (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters)
      signature.symbol nextNames (expandEquivalence signature.symbol abbreviation.reference bodyExtra) =
      some (.assertion (rename (Rename.lift rho) body)) := by
    simp [bodyExtra, holds, applySymbol, Preterm.applyArgs, expandEquivalence, readJudgmentWith,
      readHead_reference signature.symbol signature.symbol_injective, bodyRead, expect_same, nextNames, root]
  let childLogical : Judgment Const (domain :: delta) :=
    .conjunction (.conjunction (logical.rename shift) (.typing (Term.var .vz))) (.assertion (rename (Rename.lift rho) body))
  have contextRead : readJudgmentWith (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters)
      signature.symbol nextNames (expandEquivalence signature.symbol abbreviation.reference childScope.logical) = some childLogical := by
    simp [childScope, HOLKernelStructuralRules.ProofContext.under, conjunction, applySymbol, Preterm.applyArgs,
      expandEquivalence, distinct, readJudgmentWith, readHead_reference signature.symbol signature.symbol_injective,
      childLogicalRead, extraRead, bodyExtraRead, childLogical]
  have parentLogicalFormula : readFormulaIn abbreviation (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters)
      parameters nextNames scope.logical = some (logical.rename shift).formula := by
    simp only [readFormulaIn, childLogicalRead, Option.map_some]
  have parentFormationFormula : readFormulaIn abbreviation (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters)
      parameters nextNames scope.formation = some (formation.rename shift).formula := by
    simp only [readFormulaIn, childFormationRead, Option.map_some]
  have typeExtraFormula : readFormulaIn abbreviation (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters)
      parameters nextNames typeExtra = some .top := by simp only [readFormulaIn, extraRead, Option.map_some, Judgment.formula]
  have bodyExtraFormula : readFormulaIn abbreviation (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters)
      parameters nextNames bodyExtra = some (rename (Rename.lift rho) body) := by simp only [readFormulaIn, bodyExtraRead, Option.map_some, Judgment.formula]
  have parentProjectionTree : AdmittedProof abbreviation theorems context
      (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) parameters ruleAt bindingAt projectionFuel nextNames
      scope.projection.val (.imp (logical.rename shift).formula (formation.rename shift).formula) := by
    rw [weakenEq] at parentProjection
    simpa only [Judgment.rename_formula, Mettapedia.Logic.HOL.rename] using parentProjection
  obtain ⟨typedProjection⟩ := HOLKernelStructuralReadback.weaken_admitted signature abbreviation (distinct .im) (distinct .an) structural
    (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) parameters nextNames ruleAt bindingAt structuralSelected
    scope.logical typeExtra scope.formation scope.logicalSorted typeExtraSorted scope.formationSorted scope.projection
    (logical.rename shift).formula .top (formation.rename shift).formula parentLogicalFormula typeExtraFormula parentFormationFormula parentProjectionTree
  have typedLogicalFormula : readFormulaIn abbreviation (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters)
      parameters nextNames (conjunction signature.symbol scope.logical typeExtra) = some (.and (logical.rename shift).formula .top) := by
    rw [HOLKernelStructuralReadback.read_conjunction abbreviation signature.symbol_injective (distinct .an), parentLogicalFormula, typeExtraFormula]
    rfl
  obtain ⟨childProjection⟩ := HOLKernelStructuralReadback.weaken_admitted signature abbreviation (distinct .im) (distinct .an) structural
    (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) parameters nextNames ruleAt bindingAt structuralSelected
    _ bodyExtra scope.formation (scope.under signature structural typeExtra typeExtraSorted).logicalSorted bodyExtraSorted scope.formationSorted
    (scope.under signature structural typeExtra typeExtraSorted).projection
    (.and (logical.rename shift).formula .top) (rename (Rename.lift rho) body) (formation.rename shift).formula
    typedLogicalFormula bodyExtraFormula parentFormationFormula typedProjection
  obtain ⟨resultFuel, ⟨resultTree⟩⟩ := rebindInContext_admitted signature abbreviation profile structural typing rules binding
    distinct dictionary indices parameters lookup bounded base constant baseEq constantEq binders temporary
    baseSorted constantSorted bindersInjective temporaryInjective bindersAbove temporaryAbove baseIndependent temporaryIndependent
    result assignment childScope childWindows (Nat.le_refl _) assignmentSorted variableTyping constantTyping liftedRho nextNames nextNodup nextAbove nextAssignment
    (fun offset less {_} index => BinderNames.ne_nameOf_of_not_mem nextNames (sourceResultNames offset less) (liftedRho index))
    (fun offset less {_} index => BinderNames.ne_nameOf_of_not_mem nextNames (targetResultNames offset less) (liftedRho index))
    (fun offset less {_} index => BinderNames.ne_nameOf_of_not_mem nextNames (temporaryResultNames offset less) (liftedRho index)) childLogical (formation.rename shift)
    contextRead childFormationRead ruleAt bindingAt selected (structuralSelected .syl) (bindingSelected .abstractionRenaming) childProjection
  have sourceResultRead := HOLKernelAlphaReadback.encoded_read abbreviation profile distinct dictionary indices parameters lookup bounded
    base constant baseEq constantEq liftedRho nextNames assignment nextAssignment binders bindersInjective bindersAbove
    result childWindows.sourceDepth nextNodup nextAbove (fun offset less {_} index =>
      BinderNames.ne_nameOf_of_not_mem nextNames (sourceResultNames offset less) (liftedRho index))
  have targetResultRead := HOLKernelAlphaReadback.encoded_read abbreviation profile distinct dictionary indices parameters lookup bounded
    base constant baseEq constantEq liftedRho nextNames assignment nextAssignment binders bindersInjective bindersAbove
    result childWindows.workDepth nextNodup nextAbove (fun offset less {_} index =>
      BinderNames.ne_nameOf_of_not_mem nextNames (targetResultNames offset less) (liftedRho index))
  let convertedClaim := fun expression => entails signature.symbol childScope.logical (holds signature.symbol expression)
  let convertedBody : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := [])
      (convertedClaim (encodeWithAssignment signature.symbol base constant binders assignment (windows.workDepth + 1) result)) :=
    Eq.mp (congrArg (fun expression => CheckedProof (terms := terms) (definitions := definitions)
      (theorems := theorems) (context := context) (hypotheses := []) (convertedClaim expression)) coherence) bodyProof
  have convertedValue : convertedBody.val = bodyProof.val :=
    HOLKernelStructuralRules.CheckedProof.val_mpr convertedClaim coherence.symm bodyProof
  have bodyTree : AdmittedProof abbreviation theorems context
      (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) parameters ruleAt bindingAt bodyFuel nextNames
      convertedBody.val (.imp childLogical.formula (rename liftedRho result)) := by
    rw [convertedValue]
    simpa only [childLogical, Judgment.formula, Judgment.rename_formula, ← weakenEq, renamedResult] using bodyAdmitted
  let reversed := HOLKernelInferenceProofs.Native.symmetry signature rules (boolType signature.symbol) childScope.logical _ _
    (signature.application context .bool [] .nil) childScope.logicalSorted resultSorted childResultSorted resultEquation
  have boolRead : readType signature.symbol (expandEquivalence signature.symbol abbreviation.reference (boolType signature.symbol)) = some .prop := by
    simp [boolType, applySymbol, Preterm.applyArgs, expandEquivalence, readType, readHead_reference signature.symbol signature.symbol_injective]
  obtain ⟨reversedTree⟩ := HOLKernelCongruenceReadback.symmetry_admitted signature abbreviation profile distinct dictionary parameters rules nextNames
    _ childScope.logical _ _ (signature.application context .bool [] .nil) childScope.logicalSorted resultSorted childResultSorted resultEquation
    childLogical (rename liftedRho result) (rename liftedRho result) contextRead boolRead sourceResultRead targetResultRead
    ruleAt bindingAt (selected .symmetry) resultTree
  let parentConclusion := HOLKernelInferenceProofs.booleanEqualityElimination signature abbreviation rules childScope.logical _ _
    childScope.logicalSorted childResultSorted resultSorted reversed convertedBody
  obtain ⟨parentTree⟩ := HOLKernelCongruenceReadback.booleanEqualityElimination_admitted signature abbreviation profile distinct dictionary parameters
    rules nextNames childScope.logical _ _ childScope.logicalSorted childResultSorted resultSorted reversed convertedBody childLogical
    (rename liftedRho result) (rename liftedRho result) contextRead targetResultRead sourceResultRead ruleAt bindingAt
    (selected .booleanEqualityElimination) reversedTree bodyTree
  have nativeSourceRead := HOLKernelAlphaReadback.encoded_read abbreviation profile distinct dictionary indices parameters lookup bounded
    base constant baseEq constantEq rho names assignment assignmentEq binders bindersInjective bindersAbove
    result windows.sourceDepth nodup namesAbove (fun offset less {_} index =>
      BinderNames.ne_nameOf_of_not_mem names (sourceNames offset (by omega)) (rho index))
  have conclusionRead : readFormulaIn abbreviation (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters)
      parameters names (entails signature.symbol scope.logical (holds signature.symbol
        (encodeWithAssignment signature.symbol base constant binders assignment windows.sourceDepth result))) =
      some (.imp logical.formula (rename rho result)) := by
    rw [HOLKernelStructuralReadback.read_entails abbreviation signature.symbol_injective (distinct .im)]
    simp [readFormulaIn, logicalRead, holds, applySymbol, Preterm.applyArgs, expandEquivalence, readJudgmentWith,
      readHead_reference signature.symbol signature.symbol_injective, nativeSourceRead, expect_same, Judgment.formula]
  let compiled := HOLKernelBindingProofs.Native.existentialElimination signature binding scope.logical _ root _ _
    scope.logicalSorted domainSorted head bodySorted resultSorted logicalFresh
    (HOLKernelTypeSupport.encodeType_independent context _ signature.symbol base (baseIndependent _) domain)
    resultIndependent resultTyping workExists parentConclusion
  let joinedFuel := max (max (equationFuel + 1) existentialFuel + 1) (max (resultFuel + 1 + 1) bodyFuel + 1)
  have parentTree' : AdmittedProof abbreviation theorems context
      (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) parameters ruleAt bindingAt
      (max (resultFuel + 1 + 1) bodyFuel + 1) nextNames parentConclusion.val
      (.imp (.and (.and (weaken (σ := domain) logical.formula) .top) (rename (Rename.lift rho) body))
        (weaken (σ := domain) (rename rho result))) := by
    simpa only [childLogical, Judgment.formula, Judgment.rename_formula, ← weakenEq, renamedResult] using parentTree
  refine ⟨joinedFuel + 1, ?_⟩
  exact ⟨AdmittedStep.binding compiled.property.eval {
    rule := .existentialElimination
    selected := bindingSelected .existentialElimination
    declared := binding.declared .existentialElimination
    conclusion_read := conclusionRead
    step := .existentialElimination (existsTree.weakenFuel (Nat.le_max_left _ _)) fresh
      (parentTree'.weakenFuel (Nat.le_max_right _ _)) }⟩

#print axioms existentialElimination_admitted
end Mettapedia.Languages.MM0.HOLKernelSourceBindingReadback
