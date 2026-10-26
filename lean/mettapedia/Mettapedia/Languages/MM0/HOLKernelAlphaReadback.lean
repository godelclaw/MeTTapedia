import Mettapedia.Languages.MM0.HOLKernelProofReadbackRenaming
import Mettapedia.Languages.MM0.HOLKernelLogicalCongruenceReadback
/-!
# Contextual readback of the actual native alpha-renaming receipts

The two-window construction preserves independent admission for every HOL
term constructor. The three-window rebinding construction composes two such
receipts through native transitivity. An arbitrary source renaming relates the
original assignment to the reader's context; free names may occur outside the
used binder windows. Freshness protects the names of source variables in the
reader context; unrelated target names may be shadowed. All native children remain checked, while change-of-variable
readback can reconstruct reflexive source equality and forget proof identity.

The hypotheses specify the actual table profiles, parameter lookup, assignment,
native sorting and independence, and finite name freshness. No input source
proof or alpha equation supplies the admission conclusion.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.MM0.HOLKernelAlphaReadback
open Mettapedia.Logic.HOL Kernel HOLKernelSyntax HOLKernelTermReadback
open NamedElaboration (BinderNames)
open HOLKernelRuleReadback HOLKernelTermAssignments HOLKernelJudgmentReadback HOLKernelProofReadback
universe u
variable {Const : Ty Unit → Type u} {gamma : Ctx Unit}
variable {sorts : SortSignature} {terms : TermSignature} {definitions : Definition.Signature}
variable {theorems : TheoremSignature} {signature : Signature sorts terms} {context : Context}

/-- Exact encoded reading under pointwise source-variable lookup, allowing unrelated target names to be shadowed. -/
theorem encoded_read_of_lookup
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (distinct : ∀ symbol, signature.symbol symbol ≠ abbreviation.reference)
    (constants : Nat → Option (NamedElaboration.SomeConst Const))
    (indices : ∀ {type}, Const type → Nat) (parameters : Nat)
    (lookup : ∀ {type} (constant : Const type), constants (indices constant) = some ⟨type, constant⟩)
    (bounded : ∀ {type} (constant : Const type), indices constant < parameters)
    (base : Unit → Preterm) (constant : ∀ {type}, Const type → Preterm)
    (baseEq : base = fun _ => .var 0) (constantEq : ∀ {type} (symbol : Const type), constant symbol = .var (indices symbol))
    {delta : Ctx Unit} (rho : Rename Unit gamma delta) (names : Names delta) (assignment : Assignment gamma)
    (assignmentEq : ∀ {type} (index : Var gamma type), assignment index = .var (names.nameOf (rho index)))
    (binders : Nat → Nat) (injective : Function.Injective binders) (above : ∀ level, parameters ≤ binders level)
    {type : Ty Unit} (source : Term Const gamma type) (depth : Nat)
    (variablesRead : ∀ {type} (index : Var gamma type), names.lookup? (names.nameOf (rho index)) = some ⟨type, rho index⟩)
    (constantsAbsent : ∀ {type} (symbol : Const type), names.lookup? (indices symbol) = none)
    (fresh : ∀ offset < source.binderDepth, ∀ {type} (index : Var gamma type), binders (depth + offset) ≠ names.nameOf (rho index)) :
    HOLKernelLogicalFunctionReadback.reader profile constants parameters names
      (expandEquivalence signature.symbol abbreviation.reference
        (encodeWithAssignment signature.symbol base constant binders assignment depth source)) = some ⟨type, rename rho source⟩ := by
  have constantsEq : (fun {type} (symbol : Const type) => constant symbol) =
      (fun {type} (symbol : Const type) => Preterm.var (indices symbol)) := by
    funext type symbol
    exact constantEq symbol
  have assignmentsEq : (fun {type} (index : Var gamma type) => assignment index) =
      (fun {type} (index : Var gamma type) => Preterm.var (names.nameOf (rho index))) := by
    funext type index
    exact assignmentEq index
  rw [assignmentsEq, baseEq, constantsEq, encode_positions]
  rw [expandEquivalence_encodeTerm_of_fixed signature.symbol abbreviation.reference distinct
    (fun _ : Unit => Preterm.var 0) (fun {_} symbol => Preterm.var (indices symbol)) binders
    (fun _ => by simp [expandEquivalence]) (fun _ => by simp [expandEquivalence])]
  exact readTermWith_encode_renamed (HOLKernelLogicalFunctionReadback.atoms profile)
    signature.symbol signature.symbol_injective constants indices parameters lookup bounded
    binders injective above source rho names (fun index => names.nameOf (rho index)) depth
    variablesRead constantsAbsent fresh

theorem encoded_read
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (distinct : ∀ symbol, signature.symbol symbol ≠ abbreviation.reference)
    (constants : Nat → Option (NamedElaboration.SomeConst Const))
    (indices : ∀ {type}, Const type → Nat) (parameters : Nat)
    (lookup : ∀ {type} (constant : Const type), constants (indices constant) = some ⟨type, constant⟩)
    (bounded : ∀ {type} (constant : Const type), indices constant < parameters)
    (base : Unit → Preterm) (constant : ∀ {type}, Const type → Preterm)
    (baseEq : base = fun _ => .var 0) (constantEq : ∀ {type} (symbol : Const type), constant symbol = .var (indices symbol))
    {delta : Ctx Unit} (rho : Rename Unit gamma delta) (names : Names delta) (assignment : Assignment gamma)
    (assignmentEq : ∀ {type} (index : Var gamma type), assignment index = .var (names.nameOf (rho index)))
    (binders : Nat → Nat) (injective : Function.Injective binders) (above : ∀ level, parameters ≤ binders level)
    {type : Ty Unit} (source : Term Const gamma type) (depth : Nat)
    (nodup : names.toList.Nodup) (namesAbove : ∀ name ∈ names.toList, parameters ≤ name)
    (fresh : ∀ offset < source.binderDepth, ∀ {type} (index : Var gamma type), binders (depth + offset) ≠ names.nameOf (rho index)) :
    HOLKernelLogicalFunctionReadback.reader profile constants parameters names
      (expandEquivalence signature.symbol abbreviation.reference
        (encodeWithAssignment signature.symbol base constant binders assignment depth source)) = some ⟨type, rename rho source⟩ := by
  apply encoded_read_of_lookup abbreviation profile distinct constants indices parameters lookup bounded
    base constant baseEq constantEq rho names assignment assignmentEq binders injective above source depth
    (fun index => BinderNames.lookup?_nameOf names nodup (rho index))
    (by
      intro type symbol
      apply BinderNames.lookup?_none_of_not_mem
      intro member
      have lower := namesAbove _ member
      have upper := bounded symbol
      omega)
    fresh

open HOLKernelAlpha
open HOLKernelTypingRules (typed boolType functionType)
open HOLKernelInferenceRules (equality)
open HOLKernelStructuralRules (CheckedProof)

theorem encoded_body_read
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (distinct : ∀ symbol, signature.symbol symbol ≠ abbreviation.reference)
    (dictionary : Nat → Option (NamedElaboration.SomeConst Const))
    (indices : ∀ {type}, Const type → Nat) (parameters : Nat)
    (lookup : ∀ {type} (symbol : Const type), dictionary (indices symbol) = some ⟨type, symbol⟩)
    (bounded : ∀ {type} (symbol : Const type), indices symbol < parameters)
    (base : Unit → Preterm) (constant : ∀ {type}, Const type → Preterm)
    (baseEq : base = fun _ => .var 0) (constantEq : ∀ {type} (symbol : Const type), constant symbol = .var (indices symbol))
    {delta : Ctx Unit} (rho : Rename Unit gamma delta) (names : Names delta) (assignment : Assignment gamma)
    (assignmentEq : ∀ {type} (index : Var gamma type), assignment index = .var (names.nameOf (rho index)))
    (binders : Nat → Nat) (injective : Function.Injective binders) (above : ∀ level, parameters ≤ binders level)
    {domain result : Ty Unit} (body : Term Const (domain :: gamma) result) (depth : Nat)
    (nodup : names.toList.Nodup) (namesAbove : ∀ name ∈ names.toList, parameters ≤ name)
    (fresh : ∀ offset < body.binderDepth + 1, ∀ {type} (index : Var gamma type), binders (depth + offset) ≠ names.nameOf (rho index)) :
    HOLKernelLogicalFunctionReadback.reader profile dictionary parameters
      (NamedElaboration.BinderNames.cons (type := domain) (binders depth) names)
      (expandEquivalence signature.symbol abbreviation.reference
        (encodeWithAssignment signature.symbol base constant binders
          (Assignment.extend (.var (binders depth)) assignment) (depth + 1) body)) = some ⟨result, rename (Rename.lift rho) body⟩ := by
  let next : Names (domain :: delta) := NamedElaboration.BinderNames.cons (binders depth) names
  have nextAssignment : ∀ {type} (index : Var (domain :: gamma) type),
      Assignment.extend (.var (binders depth)) assignment index = .var (next.nameOf (Rename.lift rho index)) := by
    intro type index
    cases index with
    | vz => rfl
    | vs index => exact assignmentEq index
  have nextRead : ∀ {type} (index : Var (domain :: gamma) type),
      next.lookup? (next.nameOf (Rename.lift rho index)) = some ⟨type, Rename.lift rho index⟩ := by
    intro type index
    cases index with
    | vz => simp [next, Rename.lift, BinderNames.nameOf]
    | vs index =>
        have apart : binders depth ≠ names.nameOf (rho index) := by
          simpa only [Nat.add_zero] using fresh 0 (Nat.zero_lt_succ _) index
        simp [next, Rename.lift, BinderNames.nameOf, BinderNames.lookup?_cons_of_ne apart,
          BinderNames.lookup?_nameOf names nodup (rho index)]
  have nextConstants : ∀ {type} (symbol : Const type), next.lookup? (indices symbol) = none := by
    intro type symbol
    have apart : binders depth ≠ indices symbol := by have lo := above depth; have hi := bounded symbol; omega
    have absent : names.lookup? (indices symbol) = none := by
      apply BinderNames.lookup?_none_of_not_mem
      intro member
      have lo := namesAbove _ member
      have hi := bounded symbol
      omega
    simp [next, BinderNames.lookup?_cons_of_ne apart, absent]
  have nextFresh : ∀ offset < body.binderDepth, ∀ {type} (index : Var (domain :: gamma) type),
      binders (depth + 1 + offset) ≠ next.nameOf (Rename.lift rho index) := by
    intro offset less type index
    cases index with
    | vz =>
        intro same
        have impossible := injective same
        change depth + 1 + offset = depth at impossible
        omega
    | vs index =>
        have apart := fresh (offset + 1) (Nat.add_lt_add_right less 1) index
        simpa only [next, BinderNames.nameOf, Rename.lift, Nat.add_assoc, Nat.add_comm 1 offset] using apart
  exact encoded_read_of_lookup abbreviation profile distinct dictionary indices parameters lookup bounded base constant
    baseEq constantEq (Rename.lift rho) next _ nextAssignment binders injective above body (depth + 1)
    nextRead nextConstants nextFresh

theorem alphaDisjoint_lambda_admitted (signature : Signature sorts terms)
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
    (base : Unit → Preterm) (constant : ∀ {type}, Const type → Preterm)
    (baseEq : base = fun _ => .var 0)
    (constantEq : ∀ {type} (symbol : Const type), constant symbol = .var (indices symbol))
    (leftBinders rightBinders : Nat → Nat)
    (baseSorted : ∀ index, Preterm.HasType terms context (base index) [] signature.ids.type)
    (constantSorted : ∀ {type} (symbol : Const type), Preterm.HasType terms context (constant symbol) [] signature.ids.object)
    (leftInjective : Function.Injective leftBinders) (rightInjective : Function.Injective rightBinders)
    (leftAbove : ∀ level, parameters ≤ leftBinders level)
    (rightAbove : ∀ level, parameters ≤ rightBinders level)
    (baseIndependentLeft : ∀ slot index, ¬ Preterm.HasVar context (leftBinders slot) (base index))
    (baseIndependentRight : ∀ slot index, ¬ Preterm.HasVar context (rightBinders slot) (base index))
    {gamma : Ctx Unit} {domain result : Ty Unit} (body : Term Const (domain :: gamma) result) :
    ∀ (assignment : Assignment gamma) (leftDepth rightDepth : Nat) (antecedent : Preterm)
      (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
      (assignmentSorted : ∀ {type} (index : Var gamma type), Preterm.HasType terms context (assignment index) [] signature.ids.object)
      (leftSlots : ∀ offset < (Term.lam body).binderDepth, context[leftBinders (leftDepth + offset)]? = some (.bound signature.ids.object))
      (rightSlots : ∀ offset < (Term.lam body).binderDepth, context[rightBinders (rightDepth + offset)]? = some (.bound signature.ids.object))
      (leftFresh : ∀ offset < (Term.lam body).binderDepth, ¬ Preterm.HasVar context (leftBinders (leftDepth + offset)) antecedent)
      (rightFresh : ∀ offset < (Term.lam body).binderDepth, ¬ Preterm.HasVar context (rightBinders (rightDepth + offset)) antecedent)
      (disjoint : ∀ leftOffset < (Term.lam body).binderDepth, ∀ rightOffset < (Term.lam body).binderDepth,
        leftBinders (leftDepth + leftOffset) ≠ rightBinders (rightDepth + rightOffset))
      (variableTyping : ∀ {type} (index : Var gamma type),
        CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
          (context := context) (hypotheses := [])
          (typed signature.symbol antecedent (assignment index) (encodeType signature.symbol base type)))
      (constantTyping : ∀ {type} (symbol : Const type),
        CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
          (context := context) (hypotheses := [])
          (typed signature.symbol antecedent (constant symbol) (encodeType signature.symbol base type)))
      {delta : Ctx Unit} (rho : Rename Unit gamma delta) (names : Names delta) (_ : names.toList.Nodup)
      (_ : ∀ name ∈ names.toList, parameters ≤ name)
      (_ : ∀ {type} (index : Var gamma type), assignment index = .var (names.nameOf (rho index)))
      (_ : ∀ offset < (Term.lam body).binderDepth, ∀ {type} (index : Var gamma type), leftBinders (leftDepth + offset) ≠ names.nameOf (rho index))
      (_ : ∀ offset < (Term.lam body).binderDepth, ∀ {type} (index : Var gamma type), rightBinders (rightDepth + offset) ≠ names.nameOf (rho index))
      (g : Judgment Const delta)
      (_ : readJudgmentWith (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters)
        signature.symbol names (expandEquivalence signature.symbol abbreviation.reference antecedent) = some g)
      (ruleAt : Nat → Option HOLKernelRuleReadback.Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
      (_ : bindingAt (binding.index .abstractionRenaming) = some .abstractionRenaming),
      ∃ fuel, Nonempty (AdmittedProof abbreviation theorems context
        (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) parameters ruleAt bindingAt fuel names
        (alphaDisjoint signature profile structural typing rules binding base constant leftBinders rightBinders
          baseSorted constantSorted leftInjective rightInjective baseIndependentLeft baseIndependentRight (Term.lam body)
          assignment leftDepth rightDepth antecedent antecedentSorted assignmentSorted leftSlots rightSlots
          leftFresh rightFresh disjoint variableTyping constantTyping).val (.imp g.formula (.eq (rename rho (Term.lam body)) (rename rho (Term.lam body))))) := by
  have typeRead (type : Ty Unit) : readType signature.symbol
      (expandEquivalence signature.symbol abbreviation.reference (encodeType signature.symbol base type)) = some type := by
    rw [baseEq, expandEquivalence_encodeType_of_fixed signature.symbol abbreviation.reference distinct
      (fun _ : Unit => .var 0) (fun _ => by simp [expandEquivalence])]
    exact readType_encode signature.symbol signature.symbol_injective type
  intro assignment leftDepth rightDepth antecedent antecedentSorted assignmentSorted leftSlots rightSlots
    leftFresh rightFresh disjoint variableTyping constantTyping delta rho names nodup namesAbove assignmentEq
    leftNames rightNames g contextRead ruleAt bindingAt bindingSelected
  let compiled := alphaDisjoint signature profile structural typing rules binding base constant leftBinders rightBinders
    baseSorted constantSorted leftInjective rightInjective baseIndependentLeft baseIndependentRight (.lam body)
    assignment leftDepth rightDepth antecedent antecedentSorted assignmentSorted leftSlots rightSlots
    leftFresh rightFresh disjoint variableTyping constantTyping
  have leftRead := encoded_read abbreviation profile distinct dictionary indices parameters lookup bounded
    base constant baseEq constantEq rho names assignment assignmentEq leftBinders leftInjective leftAbove
    (.lam body) leftDepth nodup namesAbove leftNames
  have rightRead := encoded_read abbreviation profile distinct dictionary indices parameters lookup bounded
    base constant baseEq constantEq rho names assignment assignmentEq rightBinders rightInjective rightAbove
    (.lam body) rightDepth nodup namesAbove rightNames
  have equalityRead := HOLKernelCongruenceReadback.equation_read signature abbreviation profile distinct dictionary parameters
    names (encodeType signature.symbol base (domain ⇒ result)) _ _ (.lam (rename (Rename.lift rho) body)) (.lam (rename (Rename.lift rho) body)) (typeRead _) leftRead rightRead
  have antecedentRead : readFormulaIn abbreviation (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters)
      parameters names antecedent = some g.formula := by
    simp only [readFormulaIn, contextRead, Option.map_some]
  have conclusionRead : readFormulaIn abbreviation (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters)
      parameters names
      (HOLKernelJudgment.entails signature.symbol antecedent (HOLKernelJudgment.holds signature.symbol
        (equality signature.symbol (encodeType signature.symbol base (domain ⇒ result))
          (encodeWithAssignment signature.symbol base constant leftBinders assignment leftDepth (.lam body))
          (encodeWithAssignment signature.symbol base constant rightBinders assignment rightDepth (.lam body))))) =
      some (.imp g.formula (.eq (.lam (rename (Rename.lift rho) body)) (.lam (rename (Rename.lift rho) body)))) := by
    rw [HOLKernelStructuralReadback.read_entails abbreviation signature.symbol_injective (distinct .im),
      antecedentRead, equalityRead]
    rfl
  refine ⟨1, ?_⟩
  simp only [Mettapedia.Logic.HOL.rename]
  exact ⟨AdmittedStep.binding compiled.property.eval {
    rule := .abstractionRenaming
    selected := bindingSelected
    declared := binding.declared .abstractionRenaming
    conclusion_read := conclusionRead
    step := .abstractionRenaming }⟩

theorem alphaDisjoint_admitted (signature : Signature sorts terms)
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
    (base : Unit → Preterm) (constant : ∀ {type}, Const type → Preterm)
    (baseEq : base = fun _ => .var 0)
    (constantEq : ∀ {type} (symbol : Const type), constant symbol = .var (indices symbol))
    (leftBinders rightBinders : Nat → Nat)
    (baseSorted : ∀ index, Preterm.HasType terms context (base index) [] signature.ids.type)
    (constantSorted : ∀ {type} (symbol : Const type), Preterm.HasType terms context (constant symbol) [] signature.ids.object)
    (leftInjective : Function.Injective leftBinders) (rightInjective : Function.Injective rightBinders)
    (leftAbove : ∀ level, parameters ≤ leftBinders level)
    (rightAbove : ∀ level, parameters ≤ rightBinders level)
    (baseIndependentLeft : ∀ slot index, ¬ Preterm.HasVar context (leftBinders slot) (base index))
    (baseIndependentRight : ∀ slot index, ¬ Preterm.HasVar context (rightBinders slot) (base index))
    {gamma : Ctx Unit} {type : Ty Unit} (source : Term Const gamma type) :
    ∀ (assignment : Assignment gamma) (leftDepth rightDepth : Nat) (antecedent : Preterm)
      (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
      (assignmentSorted : ∀ {type} (index : Var gamma type), Preterm.HasType terms context (assignment index) [] signature.ids.object)
      (leftSlots : ∀ offset < source.binderDepth, context[leftBinders (leftDepth + offset)]? = some (.bound signature.ids.object))
      (rightSlots : ∀ offset < source.binderDepth, context[rightBinders (rightDepth + offset)]? = some (.bound signature.ids.object))
      (leftFresh : ∀ offset < source.binderDepth, ¬ Preterm.HasVar context (leftBinders (leftDepth + offset)) antecedent)
      (rightFresh : ∀ offset < source.binderDepth, ¬ Preterm.HasVar context (rightBinders (rightDepth + offset)) antecedent)
      (disjoint : ∀ leftOffset < source.binderDepth, ∀ rightOffset < source.binderDepth,
        leftBinders (leftDepth + leftOffset) ≠ rightBinders (rightDepth + rightOffset))
      (variableTyping : ∀ {type} (index : Var gamma type),
        CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
          (context := context) (hypotheses := [])
          (typed signature.symbol antecedent (assignment index) (encodeType signature.symbol base type)))
      (constantTyping : ∀ {type} (symbol : Const type),
        CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
          (context := context) (hypotheses := [])
          (typed signature.symbol antecedent (constant symbol) (encodeType signature.symbol base type)))
      {delta : Ctx Unit} (rho : Rename Unit gamma delta) (names : Names delta) (_ : names.toList.Nodup)
      (_ : ∀ name ∈ names.toList, parameters ≤ name)
      (_ : ∀ {type} (index : Var gamma type), assignment index = .var (names.nameOf (rho index)))
      (_ : ∀ offset < source.binderDepth, ∀ {type} (index : Var gamma type), leftBinders (leftDepth + offset) ≠ names.nameOf (rho index))
      (_ : ∀ offset < source.binderDepth, ∀ {type} (index : Var gamma type), rightBinders (rightDepth + offset) ≠ names.nameOf (rho index))
      (g : Judgment Const delta)
      (_ : readJudgmentWith (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters)
        signature.symbol names (expandEquivalence signature.symbol abbreviation.reference antecedent) = some g)
      (ruleAt : Nat → Option HOLKernelRuleReadback.Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
      (_ : ∀ rule, ruleAt (rules.index rule) = some (.inference rule))
      (_ : bindingAt (binding.index .abstractionRenaming) = some .abstractionRenaming),
      ∃ fuel, Nonempty (AdmittedProof abbreviation theorems context
        (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) parameters ruleAt bindingAt fuel names
        (alphaDisjoint signature profile structural typing rules binding base constant leftBinders rightBinders
          baseSorted constantSorted leftInjective rightInjective baseIndependentLeft baseIndependentRight source
          assignment leftDepth rightDepth antecedent antecedentSorted assignmentSorted leftSlots rightSlots
          leftFresh rightFresh disjoint variableTyping constantTyping).val (.imp g.formula (.eq (rename rho source) (rename rho source)))) := by
  have typeRead (type : Ty Unit) : readType signature.symbol
      (expandEquivalence signature.symbol abbreviation.reference (encodeType signature.symbol base type)) = some type := by
    rw [baseEq, expandEquivalence_encodeType_of_fixed signature.symbol abbreviation.reference distinct
      (fun _ : Unit => .var 0) (fun _ => by simp [expandEquivalence])]
    exact readType_encode signature.symbol signature.symbol_injective type
  induction source
  case var index =>
    intro assignment leftDepth rightDepth antecedent antecedentSorted assignmentSorted leftSlots rightSlots
      leftFresh rightFresh disjoint variableTyping constantTyping delta rho names nodup namesAbove assignmentEq
      leftNames rightNames g contextRead ruleAt bindingAt selected bindingSelected
    have reading := encoded_read abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq rho names assignment assignmentEq leftBinders leftInjective leftAbove
      (Term.var index) leftDepth nodup namesAbove leftNames
    refine ⟨2, ?_⟩
    simpa only [alphaDisjoint, encodeWithAssignment, Mettapedia.Logic.HOL.rename] using
      HOLKernelCongruenceReadback.reflexivity_admitted signature abbreviation profile distinct dictionary parameters
        rules names antecedent (encodeType signature.symbol base _) (assignment index) antecedentSorted
        (encodeType_sorted signature context base baseSorted _) (assignmentSorted index) (variableTyping index)
        g (Term.var (rho index)) contextRead (typeRead _) reading ruleAt bindingAt (selected .reflexivity)
  case const symbol =>
    intro assignment leftDepth rightDepth antecedent antecedentSorted assignmentSorted leftSlots rightSlots
      leftFresh rightFresh disjoint variableTyping constantTyping delta rho names nodup namesAbove assignmentEq
      leftNames rightNames g contextRead ruleAt bindingAt selected bindingSelected
    have reading := encoded_read abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq rho names assignment assignmentEq leftBinders leftInjective leftAbove
      (Term.const symbol) leftDepth nodup namesAbove leftNames
    refine ⟨2, ?_⟩
    simpa only [alphaDisjoint, encodeWithAssignment, Mettapedia.Logic.HOL.rename] using
      HOLKernelCongruenceReadback.reflexivity_admitted signature abbreviation profile distinct dictionary parameters
        rules names antecedent (encodeType signature.symbol base _) (constant symbol) antecedentSorted
        (encodeType_sorted signature context base baseSorted _) (constantSorted symbol) (constantTyping symbol)
        g (Term.const symbol) contextRead (typeRead _) reading ruleAt bindingAt (selected .reflexivity)
  case top =>
    intro assignment leftDepth rightDepth antecedent antecedentSorted assignmentSorted leftSlots rightSlots
      leftFresh rightFresh disjoint variableTyping constantTyping delta rho names nodup namesAbove assignmentEq
      leftNames rightNames g contextRead ruleAt bindingAt selected bindingSelected
    have reading := encoded_read abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq rho names assignment assignmentEq leftBinders leftInjective leftAbove
      (Term.top : Formula Const _) leftDepth nodup namesAbove leftNames
    refine ⟨2, ?_⟩
    simpa only [alphaDisjoint, encodeWithAssignment, encodeType, Mettapedia.Logic.HOL.rename] using
      HOLKernelCongruenceReadback.reflexivity_admitted signature abbreviation profile distinct dictionary parameters
        rules names antecedent (encodeType signature.symbol base .prop) (applySymbol signature.symbol .truth [])
        antecedentSorted (signature.application context .bool [] .nil) (signature.application context .truth [] .nil)
        (HOLKernelTypingProofs.truthTyping (hypotheses := []) signature typing antecedent antecedentSorted)
        g Term.top contextRead (typeRead _) reading ruleAt bindingAt (selected .reflexivity)
  case bot =>
    intro assignment leftDepth rightDepth antecedent antecedentSorted assignmentSorted leftSlots rightSlots
      leftFresh rightFresh disjoint variableTyping constantTyping delta rho names nodup namesAbove assignmentEq
      leftNames rightNames g contextRead ruleAt bindingAt selected bindingSelected
    have reading := encoded_read abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq rho names assignment assignmentEq leftBinders leftInjective leftAbove
      (Term.bot : Formula Const _) leftDepth nodup namesAbove leftNames
    refine ⟨2, ?_⟩
    simpa only [alphaDisjoint, encodeWithAssignment, encodeType, Mettapedia.Logic.HOL.rename] using
      HOLKernelCongruenceReadback.reflexivity_admitted signature abbreviation profile distinct dictionary parameters
        rules names antecedent (encodeType signature.symbol base .prop) (applySymbol signature.symbol .falsity [])
        antecedentSorted (signature.application context .bool [] .nil) (signature.application context .falsity [] .nil)
        (HOLKernelTypingProofs.falsityTyping (hypotheses := []) signature typing antecedent antecedentSorted)
        g Term.bot contextRead (typeRead _) reading ruleAt bindingAt (selected .reflexivity)
  case app gamma domain result first second ihFirst ihSecond =>
    intro assignment leftDepth rightDepth antecedent antecedentSorted assignmentSorted leftSlots rightSlots
      leftFresh rightFresh disjoint variableTyping constantTyping delta rho names nodup namesAbove assignmentEq
      leftNames rightNames g contextRead ruleAt bindingAt selected bindingSelected
    have firstLeftSlots := fun offset smaller => leftSlots offset
      (Nat.lt_of_lt_of_le smaller (Nat.le_max_left first.binderDepth second.binderDepth))
    have secondLeftSlots := fun offset smaller => leftSlots offset
      (Nat.lt_of_lt_of_le smaller (Nat.le_max_right first.binderDepth second.binderDepth))
    have firstRightSlots := fun offset smaller => rightSlots offset
      (Nat.lt_of_lt_of_le smaller (Nat.le_max_left first.binderDepth second.binderDepth))
    have secondRightSlots := fun offset smaller => rightSlots offset
      (Nat.lt_of_lt_of_le smaller (Nat.le_max_right first.binderDepth second.binderDepth))
    have firstLeftFresh := fun offset smaller => leftFresh offset
      (Nat.lt_of_lt_of_le smaller (Nat.le_max_left first.binderDepth second.binderDepth))
    have secondLeftFresh := fun offset smaller => leftFresh offset
      (Nat.lt_of_lt_of_le smaller (Nat.le_max_right first.binderDepth second.binderDepth))
    have firstRightFresh := fun offset smaller => rightFresh offset
      (Nat.lt_of_lt_of_le smaller (Nat.le_max_left first.binderDepth second.binderDepth))
    have secondRightFresh := fun offset smaller => rightFresh offset
      (Nat.lt_of_lt_of_le smaller (Nat.le_max_right first.binderDepth second.binderDepth))
    have firstDisjoint := fun leftOffset leftSmaller rightOffset rightSmaller =>
      disjoint leftOffset (Nat.lt_of_lt_of_le leftSmaller (Nat.le_max_left first.binderDepth second.binderDepth))
        rightOffset (Nat.lt_of_lt_of_le rightSmaller (Nat.le_max_left first.binderDepth second.binderDepth))
    have secondDisjoint := fun leftOffset leftSmaller rightOffset rightSmaller =>
      disjoint leftOffset (Nat.lt_of_lt_of_le leftSmaller (Nat.le_max_right first.binderDepth second.binderDepth))
        rightOffset (Nat.lt_of_lt_of_le rightSmaller (Nat.le_max_right first.binderDepth second.binderDepth))
    have leftFirstSorted := encode_sorted signature context base constant leftBinders
      baseSorted constantSorted first assignment leftDepth assignmentSorted firstLeftSlots
    have rightFirstSorted := encode_sorted signature context base constant rightBinders
      baseSorted constantSorted first assignment rightDepth assignmentSorted firstRightSlots
    let firstProof := alphaDisjoint signature profile structural typing rules binding base constant
      leftBinders rightBinders baseSorted constantSorted leftInjective rightInjective
      baseIndependentLeft baseIndependentRight first assignment leftDepth rightDepth antecedent
      antecedentSorted assignmentSorted firstLeftSlots firstRightSlots
      firstLeftFresh firstRightFresh firstDisjoint variableTyping constantTyping
    have leftSecondSorted := encode_sorted signature context base constant leftBinders
      baseSorted constantSorted second assignment leftDepth assignmentSorted secondLeftSlots
    have rightSecondSorted := encode_sorted signature context base constant rightBinders
      baseSorted constantSorted second assignment rightDepth assignmentSorted secondRightSlots
    let secondProof := alphaDisjoint signature profile structural typing rules binding base constant
      leftBinders rightBinders baseSorted constantSorted leftInjective rightInjective
      baseIndependentLeft baseIndependentRight second assignment leftDepth rightDepth antecedent
      antecedentSorted assignmentSorted secondLeftSlots secondRightSlots
      secondLeftFresh secondRightFresh secondDisjoint variableTyping constantTyping
    have firstLeftNames := fun offset less {type} (index : Var gamma type) => leftNames offset (Nat.lt_of_lt_of_le less (Nat.le_max_left _ _)) index
    have firstRightNames := fun offset less {type} (index : Var gamma type) => rightNames offset (Nat.lt_of_lt_of_le less (Nat.le_max_left _ _)) index
    have secondLeftNames := fun offset less {type} (index : Var gamma type) => leftNames offset (Nat.lt_of_lt_of_le less (Nat.le_max_right _ _)) index
    have secondRightNames := fun offset less {type} (index : Var gamma type) => rightNames offset (Nat.lt_of_lt_of_le less (Nat.le_max_right _ _)) index
    obtain ⟨fuelFirst, ⟨firstTree⟩⟩ := ihFirst assignment leftDepth rightDepth antecedent antecedentSorted assignmentSorted
      firstLeftSlots firstRightSlots firstLeftFresh firstRightFresh firstDisjoint variableTyping constantTyping
      rho names nodup namesAbove assignmentEq firstLeftNames firstRightNames g contextRead ruleAt bindingAt selected bindingSelected
    obtain ⟨fuelSecond, ⟨secondTree⟩⟩ := ihSecond assignment leftDepth rightDepth antecedent antecedentSorted assignmentSorted
      secondLeftSlots secondRightSlots secondLeftFresh secondRightFresh secondDisjoint variableTyping constantTyping
      rho names nodup namesAbove assignmentEq secondLeftNames secondRightNames g contextRead ruleAt bindingAt selected bindingSelected
    have firstLeftRead := encoded_read abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq rho names assignment assignmentEq leftBinders leftInjective leftAbove
      first leftDepth nodup namesAbove firstLeftNames
    have firstRightRead := encoded_read abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq rho names assignment assignmentEq rightBinders rightInjective rightAbove
      first rightDepth nodup namesAbove firstRightNames
    have secondLeftRead := encoded_read abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq rho names assignment assignmentEq leftBinders leftInjective leftAbove
      second leftDepth nodup namesAbove secondLeftNames
    have secondRightRead := encoded_read abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq rho names assignment assignmentEq rightBinders rightInjective rightAbove
      second rightDepth nodup namesAbove secondRightNames
    simp only [alphaDisjoint, Mettapedia.Logic.HOL.rename]
    exact HOLKernelCongruenceReadback.application_admitted signature abbreviation profile distinct dictionary parameters
      rules binding names antecedent (encodeType signature.symbol base domain) (encodeType signature.symbol base result)
      _ _ _ _ antecedentSorted (encodeType_sorted signature context base baseSorted domain)
      (encodeType_sorted signature context base baseSorted result) leftFirstSorted rightFirstSorted leftSecondSorted rightSecondSorted
      firstProof secondProof g (rename rho first) (rename rho first) (rename rho second) (rename rho second) contextRead (typeRead domain) (typeRead result)
      firstLeftRead firstRightRead secondLeftRead secondRightRead ruleAt bindingAt selected firstTree secondTree
  case and gamma first second ihFirst ihSecond =>
    intro assignment leftDepth rightDepth antecedent antecedentSorted assignmentSorted leftSlots rightSlots
      leftFresh rightFresh disjoint variableTyping constantTyping delta rho names nodup namesAbove assignmentEq
      leftNames rightNames g contextRead ruleAt bindingAt selected bindingSelected
    have firstLeftSlots := fun offset smaller => leftSlots offset
      (Nat.lt_of_lt_of_le smaller (Nat.le_max_left first.binderDepth second.binderDepth))
    have secondLeftSlots := fun offset smaller => leftSlots offset
      (Nat.lt_of_lt_of_le smaller (Nat.le_max_right first.binderDepth second.binderDepth))
    have firstRightSlots := fun offset smaller => rightSlots offset
      (Nat.lt_of_lt_of_le smaller (Nat.le_max_left first.binderDepth second.binderDepth))
    have secondRightSlots := fun offset smaller => rightSlots offset
      (Nat.lt_of_lt_of_le smaller (Nat.le_max_right first.binderDepth second.binderDepth))
    have firstLeftFresh := fun offset smaller => leftFresh offset
      (Nat.lt_of_lt_of_le smaller (Nat.le_max_left first.binderDepth second.binderDepth))
    have secondLeftFresh := fun offset smaller => leftFresh offset
      (Nat.lt_of_lt_of_le smaller (Nat.le_max_right first.binderDepth second.binderDepth))
    have firstRightFresh := fun offset smaller => rightFresh offset
      (Nat.lt_of_lt_of_le smaller (Nat.le_max_left first.binderDepth second.binderDepth))
    have secondRightFresh := fun offset smaller => rightFresh offset
      (Nat.lt_of_lt_of_le smaller (Nat.le_max_right first.binderDepth second.binderDepth))
    have firstDisjoint := fun leftOffset leftSmaller rightOffset rightSmaller =>
      disjoint leftOffset (Nat.lt_of_lt_of_le leftSmaller (Nat.le_max_left first.binderDepth second.binderDepth))
        rightOffset (Nat.lt_of_lt_of_le rightSmaller (Nat.le_max_left first.binderDepth second.binderDepth))
    have secondDisjoint := fun leftOffset leftSmaller rightOffset rightSmaller =>
      disjoint leftOffset (Nat.lt_of_lt_of_le leftSmaller (Nat.le_max_right first.binderDepth second.binderDepth))
        rightOffset (Nat.lt_of_lt_of_le rightSmaller (Nat.le_max_right first.binderDepth second.binderDepth))
    have leftFirstSorted := encode_sorted signature context base constant leftBinders
      baseSorted constantSorted first assignment leftDepth assignmentSorted firstLeftSlots
    have rightFirstSorted := encode_sorted signature context base constant rightBinders
      baseSorted constantSorted first assignment rightDepth assignmentSorted firstRightSlots
    let firstProof := alphaDisjoint signature profile structural typing rules binding base constant
      leftBinders rightBinders baseSorted constantSorted leftInjective rightInjective
      baseIndependentLeft baseIndependentRight first assignment leftDepth rightDepth antecedent
      antecedentSorted assignmentSorted firstLeftSlots firstRightSlots
      firstLeftFresh firstRightFresh firstDisjoint variableTyping constantTyping
    have leftSecondSorted := encode_sorted signature context base constant leftBinders
      baseSorted constantSorted second assignment leftDepth assignmentSorted secondLeftSlots
    have rightSecondSorted := encode_sorted signature context base constant rightBinders
      baseSorted constantSorted second assignment rightDepth assignmentSorted secondRightSlots
    let secondProof := alphaDisjoint signature profile structural typing rules binding base constant
      leftBinders rightBinders baseSorted constantSorted leftInjective rightInjective
      baseIndependentLeft baseIndependentRight second assignment leftDepth rightDepth antecedent
      antecedentSorted assignmentSorted secondLeftSlots secondRightSlots
      secondLeftFresh secondRightFresh secondDisjoint variableTyping constantTyping
    have firstLeftNames := fun offset less {type} (index : Var gamma type) => leftNames offset (Nat.lt_of_lt_of_le less (Nat.le_max_left _ _)) index
    have firstRightNames := fun offset less {type} (index : Var gamma type) => rightNames offset (Nat.lt_of_lt_of_le less (Nat.le_max_left _ _)) index
    have secondLeftNames := fun offset less {type} (index : Var gamma type) => leftNames offset (Nat.lt_of_lt_of_le less (Nat.le_max_right _ _)) index
    have secondRightNames := fun offset less {type} (index : Var gamma type) => rightNames offset (Nat.lt_of_lt_of_le less (Nat.le_max_right _ _)) index
    obtain ⟨fuelFirst, ⟨firstTree⟩⟩ := ihFirst assignment leftDepth rightDepth antecedent antecedentSorted assignmentSorted
      firstLeftSlots firstRightSlots firstLeftFresh firstRightFresh firstDisjoint variableTyping constantTyping
      rho names nodup namesAbove assignmentEq firstLeftNames firstRightNames g contextRead ruleAt bindingAt selected bindingSelected
    obtain ⟨fuelSecond, ⟨secondTree⟩⟩ := ihSecond assignment leftDepth rightDepth antecedent antecedentSorted assignmentSorted
      secondLeftSlots secondRightSlots secondLeftFresh secondRightFresh secondDisjoint variableTyping constantTyping
      rho names nodup namesAbove assignmentEq secondLeftNames secondRightNames g contextRead ruleAt bindingAt selected bindingSelected
    have firstLeftRead := encoded_read abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq rho names assignment assignmentEq leftBinders leftInjective leftAbove
      first leftDepth nodup namesAbove firstLeftNames
    have firstRightRead := encoded_read abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq rho names assignment assignmentEq rightBinders rightInjective rightAbove
      first rightDepth nodup namesAbove firstRightNames
    have secondLeftRead := encoded_read abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq rho names assignment assignmentEq leftBinders leftInjective leftAbove
      second leftDepth nodup namesAbove secondLeftNames
    have secondRightRead := encoded_read abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq rho names assignment assignmentEq rightBinders rightInjective rightAbove
      second rightDepth nodup namesAbove secondRightNames
    simp only [alphaDisjoint, Mettapedia.Logic.HOL.rename]
    exact HOLKernelCongruenceReadback.conjunction_admitted signature abbreviation profile distinct dictionary parameters
      rules binding names antecedent _ _ _ _ antecedentSorted leftFirstSorted rightFirstSorted leftSecondSorted rightSecondSorted
      firstProof secondProof g (rename rho first) (rename rho first) (rename rho second) (rename rho second) contextRead firstLeftRead firstRightRead secondLeftRead secondRightRead
      ruleAt bindingAt selected firstTree secondTree
  case or gamma first second ihFirst ihSecond =>
    intro assignment leftDepth rightDepth antecedent antecedentSorted assignmentSorted leftSlots rightSlots
      leftFresh rightFresh disjoint variableTyping constantTyping delta rho names nodup namesAbove assignmentEq
      leftNames rightNames g contextRead ruleAt bindingAt selected bindingSelected
    have firstLeftSlots := fun offset smaller => leftSlots offset
      (Nat.lt_of_lt_of_le smaller (Nat.le_max_left first.binderDepth second.binderDepth))
    have secondLeftSlots := fun offset smaller => leftSlots offset
      (Nat.lt_of_lt_of_le smaller (Nat.le_max_right first.binderDepth second.binderDepth))
    have firstRightSlots := fun offset smaller => rightSlots offset
      (Nat.lt_of_lt_of_le smaller (Nat.le_max_left first.binderDepth second.binderDepth))
    have secondRightSlots := fun offset smaller => rightSlots offset
      (Nat.lt_of_lt_of_le smaller (Nat.le_max_right first.binderDepth second.binderDepth))
    have firstLeftFresh := fun offset smaller => leftFresh offset
      (Nat.lt_of_lt_of_le smaller (Nat.le_max_left first.binderDepth second.binderDepth))
    have secondLeftFresh := fun offset smaller => leftFresh offset
      (Nat.lt_of_lt_of_le smaller (Nat.le_max_right first.binderDepth second.binderDepth))
    have firstRightFresh := fun offset smaller => rightFresh offset
      (Nat.lt_of_lt_of_le smaller (Nat.le_max_left first.binderDepth second.binderDepth))
    have secondRightFresh := fun offset smaller => rightFresh offset
      (Nat.lt_of_lt_of_le smaller (Nat.le_max_right first.binderDepth second.binderDepth))
    have firstDisjoint := fun leftOffset leftSmaller rightOffset rightSmaller =>
      disjoint leftOffset (Nat.lt_of_lt_of_le leftSmaller (Nat.le_max_left first.binderDepth second.binderDepth))
        rightOffset (Nat.lt_of_lt_of_le rightSmaller (Nat.le_max_left first.binderDepth second.binderDepth))
    have secondDisjoint := fun leftOffset leftSmaller rightOffset rightSmaller =>
      disjoint leftOffset (Nat.lt_of_lt_of_le leftSmaller (Nat.le_max_right first.binderDepth second.binderDepth))
        rightOffset (Nat.lt_of_lt_of_le rightSmaller (Nat.le_max_right first.binderDepth second.binderDepth))
    have leftFirstSorted := encode_sorted signature context base constant leftBinders
      baseSorted constantSorted first assignment leftDepth assignmentSorted firstLeftSlots
    have rightFirstSorted := encode_sorted signature context base constant rightBinders
      baseSorted constantSorted first assignment rightDepth assignmentSorted firstRightSlots
    let firstProof := alphaDisjoint signature profile structural typing rules binding base constant
      leftBinders rightBinders baseSorted constantSorted leftInjective rightInjective
      baseIndependentLeft baseIndependentRight first assignment leftDepth rightDepth antecedent
      antecedentSorted assignmentSorted firstLeftSlots firstRightSlots
      firstLeftFresh firstRightFresh firstDisjoint variableTyping constantTyping
    have leftSecondSorted := encode_sorted signature context base constant leftBinders
      baseSorted constantSorted second assignment leftDepth assignmentSorted secondLeftSlots
    have rightSecondSorted := encode_sorted signature context base constant rightBinders
      baseSorted constantSorted second assignment rightDepth assignmentSorted secondRightSlots
    let secondProof := alphaDisjoint signature profile structural typing rules binding base constant
      leftBinders rightBinders baseSorted constantSorted leftInjective rightInjective
      baseIndependentLeft baseIndependentRight second assignment leftDepth rightDepth antecedent
      antecedentSorted assignmentSorted secondLeftSlots secondRightSlots
      secondLeftFresh secondRightFresh secondDisjoint variableTyping constantTyping
    have firstLeftNames := fun offset less {type} (index : Var gamma type) => leftNames offset (Nat.lt_of_lt_of_le less (Nat.le_max_left _ _)) index
    have firstRightNames := fun offset less {type} (index : Var gamma type) => rightNames offset (Nat.lt_of_lt_of_le less (Nat.le_max_left _ _)) index
    have secondLeftNames := fun offset less {type} (index : Var gamma type) => leftNames offset (Nat.lt_of_lt_of_le less (Nat.le_max_right _ _)) index
    have secondRightNames := fun offset less {type} (index : Var gamma type) => rightNames offset (Nat.lt_of_lt_of_le less (Nat.le_max_right _ _)) index
    obtain ⟨fuelFirst, ⟨firstTree⟩⟩ := ihFirst assignment leftDepth rightDepth antecedent antecedentSorted assignmentSorted
      firstLeftSlots firstRightSlots firstLeftFresh firstRightFresh firstDisjoint variableTyping constantTyping
      rho names nodup namesAbove assignmentEq firstLeftNames firstRightNames g contextRead ruleAt bindingAt selected bindingSelected
    obtain ⟨fuelSecond, ⟨secondTree⟩⟩ := ihSecond assignment leftDepth rightDepth antecedent antecedentSorted assignmentSorted
      secondLeftSlots secondRightSlots secondLeftFresh secondRightFresh secondDisjoint variableTyping constantTyping
      rho names nodup namesAbove assignmentEq secondLeftNames secondRightNames g contextRead ruleAt bindingAt selected bindingSelected
    have firstLeftRead := encoded_read abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq rho names assignment assignmentEq leftBinders leftInjective leftAbove
      first leftDepth nodup namesAbove firstLeftNames
    have firstRightRead := encoded_read abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq rho names assignment assignmentEq rightBinders rightInjective rightAbove
      first rightDepth nodup namesAbove firstRightNames
    have secondLeftRead := encoded_read abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq rho names assignment assignmentEq leftBinders leftInjective leftAbove
      second leftDepth nodup namesAbove secondLeftNames
    have secondRightRead := encoded_read abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq rho names assignment assignmentEq rightBinders rightInjective rightAbove
      second rightDepth nodup namesAbove secondRightNames
    simp only [alphaDisjoint, Mettapedia.Logic.HOL.rename]
    exact HOLKernelCongruenceReadback.disjunction_admitted signature abbreviation profile distinct dictionary parameters
      rules binding names antecedent _ _ _ _ antecedentSorted leftFirstSorted rightFirstSorted leftSecondSorted rightSecondSorted
      firstProof secondProof g (rename rho first) (rename rho first) (rename rho second) (rename rho second) contextRead firstLeftRead firstRightRead secondLeftRead secondRightRead
      ruleAt bindingAt selected firstTree secondTree
  case imp gamma first second ihFirst ihSecond =>
    intro assignment leftDepth rightDepth antecedent antecedentSorted assignmentSorted leftSlots rightSlots
      leftFresh rightFresh disjoint variableTyping constantTyping delta rho names nodup namesAbove assignmentEq
      leftNames rightNames g contextRead ruleAt bindingAt selected bindingSelected
    have firstLeftSlots := fun offset smaller => leftSlots offset
      (Nat.lt_of_lt_of_le smaller (Nat.le_max_left first.binderDepth second.binderDepth))
    have secondLeftSlots := fun offset smaller => leftSlots offset
      (Nat.lt_of_lt_of_le smaller (Nat.le_max_right first.binderDepth second.binderDepth))
    have firstRightSlots := fun offset smaller => rightSlots offset
      (Nat.lt_of_lt_of_le smaller (Nat.le_max_left first.binderDepth second.binderDepth))
    have secondRightSlots := fun offset smaller => rightSlots offset
      (Nat.lt_of_lt_of_le smaller (Nat.le_max_right first.binderDepth second.binderDepth))
    have firstLeftFresh := fun offset smaller => leftFresh offset
      (Nat.lt_of_lt_of_le smaller (Nat.le_max_left first.binderDepth second.binderDepth))
    have secondLeftFresh := fun offset smaller => leftFresh offset
      (Nat.lt_of_lt_of_le smaller (Nat.le_max_right first.binderDepth second.binderDepth))
    have firstRightFresh := fun offset smaller => rightFresh offset
      (Nat.lt_of_lt_of_le smaller (Nat.le_max_left first.binderDepth second.binderDepth))
    have secondRightFresh := fun offset smaller => rightFresh offset
      (Nat.lt_of_lt_of_le smaller (Nat.le_max_right first.binderDepth second.binderDepth))
    have firstDisjoint := fun leftOffset leftSmaller rightOffset rightSmaller =>
      disjoint leftOffset (Nat.lt_of_lt_of_le leftSmaller (Nat.le_max_left first.binderDepth second.binderDepth))
        rightOffset (Nat.lt_of_lt_of_le rightSmaller (Nat.le_max_left first.binderDepth second.binderDepth))
    have secondDisjoint := fun leftOffset leftSmaller rightOffset rightSmaller =>
      disjoint leftOffset (Nat.lt_of_lt_of_le leftSmaller (Nat.le_max_right first.binderDepth second.binderDepth))
        rightOffset (Nat.lt_of_lt_of_le rightSmaller (Nat.le_max_right first.binderDepth second.binderDepth))
    have leftFirstSorted := encode_sorted signature context base constant leftBinders
      baseSorted constantSorted first assignment leftDepth assignmentSorted firstLeftSlots
    have rightFirstSorted := encode_sorted signature context base constant rightBinders
      baseSorted constantSorted first assignment rightDepth assignmentSorted firstRightSlots
    let firstProof := alphaDisjoint signature profile structural typing rules binding base constant
      leftBinders rightBinders baseSorted constantSorted leftInjective rightInjective
      baseIndependentLeft baseIndependentRight first assignment leftDepth rightDepth antecedent
      antecedentSorted assignmentSorted firstLeftSlots firstRightSlots
      firstLeftFresh firstRightFresh firstDisjoint variableTyping constantTyping
    have leftSecondSorted := encode_sorted signature context base constant leftBinders
      baseSorted constantSorted second assignment leftDepth assignmentSorted secondLeftSlots
    have rightSecondSorted := encode_sorted signature context base constant rightBinders
      baseSorted constantSorted second assignment rightDepth assignmentSorted secondRightSlots
    let secondProof := alphaDisjoint signature profile structural typing rules binding base constant
      leftBinders rightBinders baseSorted constantSorted leftInjective rightInjective
      baseIndependentLeft baseIndependentRight second assignment leftDepth rightDepth antecedent
      antecedentSorted assignmentSorted secondLeftSlots secondRightSlots
      secondLeftFresh secondRightFresh secondDisjoint variableTyping constantTyping
    have firstLeftNames := fun offset less {type} (index : Var gamma type) => leftNames offset (Nat.lt_of_lt_of_le less (Nat.le_max_left _ _)) index
    have firstRightNames := fun offset less {type} (index : Var gamma type) => rightNames offset (Nat.lt_of_lt_of_le less (Nat.le_max_left _ _)) index
    have secondLeftNames := fun offset less {type} (index : Var gamma type) => leftNames offset (Nat.lt_of_lt_of_le less (Nat.le_max_right _ _)) index
    have secondRightNames := fun offset less {type} (index : Var gamma type) => rightNames offset (Nat.lt_of_lt_of_le less (Nat.le_max_right _ _)) index
    obtain ⟨fuelFirst, ⟨firstTree⟩⟩ := ihFirst assignment leftDepth rightDepth antecedent antecedentSorted assignmentSorted
      firstLeftSlots firstRightSlots firstLeftFresh firstRightFresh firstDisjoint variableTyping constantTyping
      rho names nodup namesAbove assignmentEq firstLeftNames firstRightNames g contextRead ruleAt bindingAt selected bindingSelected
    obtain ⟨fuelSecond, ⟨secondTree⟩⟩ := ihSecond assignment leftDepth rightDepth antecedent antecedentSorted assignmentSorted
      secondLeftSlots secondRightSlots secondLeftFresh secondRightFresh secondDisjoint variableTyping constantTyping
      rho names nodup namesAbove assignmentEq secondLeftNames secondRightNames g contextRead ruleAt bindingAt selected bindingSelected
    have firstLeftRead := encoded_read abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq rho names assignment assignmentEq leftBinders leftInjective leftAbove
      first leftDepth nodup namesAbove firstLeftNames
    have firstRightRead := encoded_read abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq rho names assignment assignmentEq rightBinders rightInjective rightAbove
      first rightDepth nodup namesAbove firstRightNames
    have secondLeftRead := encoded_read abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq rho names assignment assignmentEq leftBinders leftInjective leftAbove
      second leftDepth nodup namesAbove secondLeftNames
    have secondRightRead := encoded_read abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq rho names assignment assignmentEq rightBinders rightInjective rightAbove
      second rightDepth nodup namesAbove secondRightNames
    simp only [alphaDisjoint, Mettapedia.Logic.HOL.rename]
    exact HOLKernelCongruenceReadback.implication_admitted signature abbreviation profile distinct dictionary parameters
      rules binding names antecedent _ _ _ _ antecedentSorted leftFirstSorted rightFirstSorted leftSecondSorted rightSecondSorted
      firstProof secondProof g (rename rho first) (rename rho first) (rename rho second) (rename rho second) contextRead firstLeftRead firstRightRead secondLeftRead secondRightRead
      ruleAt bindingAt selected firstTree secondTree
  case eq gamma operand first second ihFirst ihSecond =>
    intro assignment leftDepth rightDepth antecedent antecedentSorted assignmentSorted leftSlots rightSlots
      leftFresh rightFresh disjoint variableTyping constantTyping delta rho names nodup namesAbove assignmentEq
      leftNames rightNames g contextRead ruleAt bindingAt selected bindingSelected
    have firstLeftSlots := fun offset smaller => leftSlots offset
      (Nat.lt_of_lt_of_le smaller (Nat.le_max_left first.binderDepth second.binderDepth))
    have secondLeftSlots := fun offset smaller => leftSlots offset
      (Nat.lt_of_lt_of_le smaller (Nat.le_max_right first.binderDepth second.binderDepth))
    have firstRightSlots := fun offset smaller => rightSlots offset
      (Nat.lt_of_lt_of_le smaller (Nat.le_max_left first.binderDepth second.binderDepth))
    have secondRightSlots := fun offset smaller => rightSlots offset
      (Nat.lt_of_lt_of_le smaller (Nat.le_max_right first.binderDepth second.binderDepth))
    have firstLeftFresh := fun offset smaller => leftFresh offset
      (Nat.lt_of_lt_of_le smaller (Nat.le_max_left first.binderDepth second.binderDepth))
    have secondLeftFresh := fun offset smaller => leftFresh offset
      (Nat.lt_of_lt_of_le smaller (Nat.le_max_right first.binderDepth second.binderDepth))
    have firstRightFresh := fun offset smaller => rightFresh offset
      (Nat.lt_of_lt_of_le smaller (Nat.le_max_left first.binderDepth second.binderDepth))
    have secondRightFresh := fun offset smaller => rightFresh offset
      (Nat.lt_of_lt_of_le smaller (Nat.le_max_right first.binderDepth second.binderDepth))
    have firstDisjoint := fun leftOffset leftSmaller rightOffset rightSmaller =>
      disjoint leftOffset (Nat.lt_of_lt_of_le leftSmaller (Nat.le_max_left first.binderDepth second.binderDepth))
        rightOffset (Nat.lt_of_lt_of_le rightSmaller (Nat.le_max_left first.binderDepth second.binderDepth))
    have secondDisjoint := fun leftOffset leftSmaller rightOffset rightSmaller =>
      disjoint leftOffset (Nat.lt_of_lt_of_le leftSmaller (Nat.le_max_right first.binderDepth second.binderDepth))
        rightOffset (Nat.lt_of_lt_of_le rightSmaller (Nat.le_max_right first.binderDepth second.binderDepth))
    have leftFirstSorted := encode_sorted signature context base constant leftBinders
      baseSorted constantSorted first assignment leftDepth assignmentSorted firstLeftSlots
    have rightFirstSorted := encode_sorted signature context base constant rightBinders
      baseSorted constantSorted first assignment rightDepth assignmentSorted firstRightSlots
    let firstProof := alphaDisjoint signature profile structural typing rules binding base constant
      leftBinders rightBinders baseSorted constantSorted leftInjective rightInjective
      baseIndependentLeft baseIndependentRight first assignment leftDepth rightDepth antecedent
      antecedentSorted assignmentSorted firstLeftSlots firstRightSlots
      firstLeftFresh firstRightFresh firstDisjoint variableTyping constantTyping
    have leftSecondSorted := encode_sorted signature context base constant leftBinders
      baseSorted constantSorted second assignment leftDepth assignmentSorted secondLeftSlots
    have rightSecondSorted := encode_sorted signature context base constant rightBinders
      baseSorted constantSorted second assignment rightDepth assignmentSorted secondRightSlots
    let secondProof := alphaDisjoint signature profile structural typing rules binding base constant
      leftBinders rightBinders baseSorted constantSorted leftInjective rightInjective
      baseIndependentLeft baseIndependentRight second assignment leftDepth rightDepth antecedent
      antecedentSorted assignmentSorted secondLeftSlots secondRightSlots
      secondLeftFresh secondRightFresh secondDisjoint variableTyping constantTyping
    have firstLeftNames := fun offset less {type} (index : Var gamma type) => leftNames offset (Nat.lt_of_lt_of_le less (Nat.le_max_left _ _)) index
    have firstRightNames := fun offset less {type} (index : Var gamma type) => rightNames offset (Nat.lt_of_lt_of_le less (Nat.le_max_left _ _)) index
    have secondLeftNames := fun offset less {type} (index : Var gamma type) => leftNames offset (Nat.lt_of_lt_of_le less (Nat.le_max_right _ _)) index
    have secondRightNames := fun offset less {type} (index : Var gamma type) => rightNames offset (Nat.lt_of_lt_of_le less (Nat.le_max_right _ _)) index
    obtain ⟨fuelFirst, ⟨firstTree⟩⟩ := ihFirst assignment leftDepth rightDepth antecedent antecedentSorted assignmentSorted
      firstLeftSlots firstRightSlots firstLeftFresh firstRightFresh firstDisjoint variableTyping constantTyping
      rho names nodup namesAbove assignmentEq firstLeftNames firstRightNames g contextRead ruleAt bindingAt selected bindingSelected
    obtain ⟨fuelSecond, ⟨secondTree⟩⟩ := ihSecond assignment leftDepth rightDepth antecedent antecedentSorted assignmentSorted
      secondLeftSlots secondRightSlots secondLeftFresh secondRightFresh secondDisjoint variableTyping constantTyping
      rho names nodup namesAbove assignmentEq secondLeftNames secondRightNames g contextRead ruleAt bindingAt selected bindingSelected
    have firstLeftRead := encoded_read abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq rho names assignment assignmentEq leftBinders leftInjective leftAbove
      first leftDepth nodup namesAbove firstLeftNames
    have firstRightRead := encoded_read abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq rho names assignment assignmentEq rightBinders rightInjective rightAbove
      first rightDepth nodup namesAbove firstRightNames
    have secondLeftRead := encoded_read abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq rho names assignment assignmentEq leftBinders leftInjective leftAbove
      second leftDepth nodup namesAbove secondLeftNames
    have secondRightRead := encoded_read abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq rho names assignment assignmentEq rightBinders rightInjective rightAbove
      second rightDepth nodup namesAbove secondRightNames
    simp only [alphaDisjoint, Mettapedia.Logic.HOL.rename]
    exact HOLKernelCongruenceReadback.equality_admitted signature abbreviation profile distinct dictionary parameters
      rules binding names antecedent (encodeType signature.symbol base operand) _ _ _ _
      antecedentSorted (encodeType_sorted signature context base baseSorted operand)
      leftFirstSorted rightFirstSorted leftSecondSorted rightSecondSorted firstProof secondProof
      g (rename rho first) (rename rho first) (rename rho second) (rename rho second) (typeRead operand) contextRead firstLeftRead firstRightRead secondLeftRead secondRightRead
      ruleAt bindingAt selected firstTree secondTree
  case not gamma body ih =>
    intro assignment leftDepth rightDepth antecedent antecedentSorted assignmentSorted leftSlots rightSlots
      leftFresh rightFresh disjoint variableTyping constantTyping delta rho names nodup namesAbove assignmentEq
      leftNames rightNames g contextRead ruleAt bindingAt selected bindingSelected
    let bodyProof := alphaDisjoint signature profile structural typing rules binding base constant leftBinders rightBinders
      baseSorted constantSorted leftInjective rightInjective baseIndependentLeft baseIndependentRight body
      assignment leftDepth rightDepth antecedent antecedentSorted assignmentSorted leftSlots rightSlots
      leftFresh rightFresh disjoint variableTyping constantTyping
    obtain ⟨fuel, ⟨tree⟩⟩ := ih assignment leftDepth rightDepth antecedent antecedentSorted assignmentSorted
      leftSlots rightSlots leftFresh rightFresh disjoint variableTyping constantTyping
      rho names nodup namesAbove assignmentEq leftNames rightNames g contextRead ruleAt bindingAt selected bindingSelected
    have leftRead := encoded_read abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq rho names assignment assignmentEq leftBinders leftInjective leftAbove
      body leftDepth nodup namesAbove leftNames
    have rightRead := encoded_read abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq rho names assignment assignmentEq rightBinders rightInjective rightAbove
      body rightDepth nodup namesAbove rightNames
    refine ⟨max 1 fuel + 2, ?_⟩
    simp only [alphaDisjoint, Mettapedia.Logic.HOL.rename]
    exact HOLKernelCongruenceReadback.negation_admitted signature abbreviation profile distinct dictionary parameters
      rules names antecedent _ _ antecedentSorted
      (encode_sorted signature context base constant leftBinders baseSorted constantSorted body
        assignment leftDepth assignmentSorted leftSlots)
      (encode_sorted signature context base constant rightBinders baseSorted constantSorted body
        assignment rightDepth assignmentSorted rightSlots)
      bodyProof g (rename rho body) (rename rho body) contextRead leftRead rightRead ruleAt bindingAt (selected .applicationArgument) tree
  case lam domain gamma result body ih =>
    intro assignment leftDepth rightDepth antecedent antecedentSorted assignmentSorted leftSlots rightSlots
      leftFresh rightFresh disjoint variableTyping constantTyping delta rho names nodup namesAbove assignmentEq
      leftNames rightNames g contextRead ruleAt bindingAt selected bindingSelected
    exact alphaDisjoint_lambda_admitted signature abbreviation profile structural typing rules binding
      distinct dictionary indices parameters lookup bounded base constant baseEq constantEq leftBinders rightBinders
      baseSorted constantSorted leftInjective rightInjective leftAbove rightAbove baseIndependentLeft baseIndependentRight
      body assignment leftDepth rightDepth antecedent antecedentSorted assignmentSorted leftSlots rightSlots
      leftFresh rightFresh disjoint variableTyping constantTyping rho names nodup namesAbove assignmentEq
      leftNames rightNames g contextRead ruleAt bindingAt bindingSelected
  case all domain gamma body ih =>
    intro assignment leftDepth rightDepth antecedent antecedentSorted assignmentSorted leftSlots rightSlots
      leftFresh rightFresh disjoint variableTyping constantTyping delta rho names nodup namesAbove assignmentEq
      leftNames rightNames g contextRead ruleAt bindingAt selected bindingSelected
    let lambdaProof := alphaDisjoint signature profile structural typing rules binding base constant leftBinders rightBinders
      baseSorted constantSorted leftInjective rightInjective baseIndependentLeft baseIndependentRight (.lam body)
      assignment leftDepth rightDepth antecedent antecedentSorted assignmentSorted leftSlots rightSlots
      leftFresh rightFresh disjoint variableTyping constantTyping
    obtain ⟨fuel, ⟨tree⟩⟩ := alphaDisjoint_lambda_admitted signature abbreviation profile structural typing rules binding
      distinct dictionary indices parameters lookup bounded base constant baseEq constantEq leftBinders rightBinders
      baseSorted constantSorted leftInjective rightInjective leftAbove rightAbove baseIndependentLeft baseIndependentRight
      body assignment leftDepth rightDepth antecedent antecedentSorted assignmentSorted leftSlots rightSlots
      leftFresh rightFresh disjoint variableTyping constantTyping rho names nodup namesAbove assignmentEq
      leftNames rightNames g contextRead ruleAt bindingAt bindingSelected
    have leftHead : context[leftBinders leftDepth]? = some (.bound signature.ids.object) := by
      simpa only [Nat.add_zero] using leftSlots 0 (Nat.zero_lt_succ _)
    have rightHead : context[rightBinders rightDepth]? = some (.bound signature.ids.object) := by
      simpa only [Nat.add_zero] using rightSlots 0 (Nat.zero_lt_succ _)
    have leftBodySlots : ∀ offset < body.binderDepth, context[leftBinders (leftDepth + 1 + offset)]? = some (.bound signature.ids.object) := by
      intro offset less
      simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using leftSlots (offset + 1) (Nat.add_lt_add_right less 1)
    have rightBodySlots : ∀ offset < body.binderDepth, context[rightBinders (rightDepth + 1 + offset)]? = some (.bound signature.ids.object) := by
      intro offset less
      simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using rightSlots (offset + 1) (Nat.add_lt_add_right less 1)
    have leftExtendedSorted : ∀ {type} (index : Var (domain :: gamma) type),
        Preterm.HasType terms context (Assignment.extend (.var (leftBinders leftDepth)) assignment index) [] signature.ids.object :=
      Assignment.extend_sorted signature context _ assignment (.var leftHead) assignmentSorted
    have rightExtendedSorted : ∀ {type} (index : Var (domain :: gamma) type),
        Preterm.HasType terms context (Assignment.extend (.var (rightBinders rightDepth)) assignment index) [] signature.ids.object :=
      Assignment.extend_sorted signature context _ assignment (.var rightHead) assignmentSorted
    have leftBodyRead := encoded_body_read abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq rho names assignment assignmentEq leftBinders leftInjective leftAbove
      body leftDepth nodup namesAbove leftNames
    have rightBodyRead := encoded_body_read abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq rho names assignment assignmentEq rightBinders rightInjective rightAbove
      body rightDepth nodup namesAbove rightNames
    refine ⟨max 1 fuel + 2, ?_⟩
    simp only [alphaDisjoint, Mettapedia.Logic.HOL.rename]
    exact HOLKernelCongruenceReadback.universal_admitted signature abbreviation profile distinct dictionary parameters
      rules names antecedent (encodeType signature.symbol base domain) _ _ (leftBinders leftDepth) (rightBinders rightDepth)
      antecedentSorted (encodeType_sorted signature context base baseSorted domain) leftHead rightHead
      (encode_sorted signature context base constant leftBinders baseSorted constantSorted body _ (leftDepth + 1) leftExtendedSorted leftBodySlots)
      (encode_sorted signature context base constant rightBinders baseSorted constantSorted body _ (rightDepth + 1) rightExtendedSorted rightBodySlots)
      lambdaProof g (rename (Rename.lift rho) body) (rename (Rename.lift rho) body) contextRead (typeRead domain) (leftAbove leftDepth) (rightAbove rightDepth)
      leftBodyRead rightBodyRead ruleAt bindingAt (selected .applicationArgument) tree
  case ex domain gamma body ih =>
    intro assignment leftDepth rightDepth antecedent antecedentSorted assignmentSorted leftSlots rightSlots
      leftFresh rightFresh disjoint variableTyping constantTyping delta rho names nodup namesAbove assignmentEq
      leftNames rightNames g contextRead ruleAt bindingAt selected bindingSelected
    let lambdaProof := alphaDisjoint signature profile structural typing rules binding base constant leftBinders rightBinders
      baseSorted constantSorted leftInjective rightInjective baseIndependentLeft baseIndependentRight (.lam body)
      assignment leftDepth rightDepth antecedent antecedentSorted assignmentSorted leftSlots rightSlots
      leftFresh rightFresh disjoint variableTyping constantTyping
    obtain ⟨fuel, ⟨tree⟩⟩ := alphaDisjoint_lambda_admitted signature abbreviation profile structural typing rules binding
      distinct dictionary indices parameters lookup bounded base constant baseEq constantEq leftBinders rightBinders
      baseSorted constantSorted leftInjective rightInjective leftAbove rightAbove baseIndependentLeft baseIndependentRight
      body assignment leftDepth rightDepth antecedent antecedentSorted assignmentSorted leftSlots rightSlots
      leftFresh rightFresh disjoint variableTyping constantTyping rho names nodup namesAbove assignmentEq
      leftNames rightNames g contextRead ruleAt bindingAt bindingSelected
    have leftHead : context[leftBinders leftDepth]? = some (.bound signature.ids.object) := by
      simpa only [Nat.add_zero] using leftSlots 0 (Nat.zero_lt_succ _)
    have rightHead : context[rightBinders rightDepth]? = some (.bound signature.ids.object) := by
      simpa only [Nat.add_zero] using rightSlots 0 (Nat.zero_lt_succ _)
    have leftBodySlots : ∀ offset < body.binderDepth, context[leftBinders (leftDepth + 1 + offset)]? = some (.bound signature.ids.object) := by
      intro offset less
      simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using leftSlots (offset + 1) (Nat.add_lt_add_right less 1)
    have rightBodySlots : ∀ offset < body.binderDepth, context[rightBinders (rightDepth + 1 + offset)]? = some (.bound signature.ids.object) := by
      intro offset less
      simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using rightSlots (offset + 1) (Nat.add_lt_add_right less 1)
    have leftExtendedSorted : ∀ {type} (index : Var (domain :: gamma) type),
        Preterm.HasType terms context (Assignment.extend (.var (leftBinders leftDepth)) assignment index) [] signature.ids.object :=
      Assignment.extend_sorted signature context _ assignment (.var leftHead) assignmentSorted
    have rightExtendedSorted : ∀ {type} (index : Var (domain :: gamma) type),
        Preterm.HasType terms context (Assignment.extend (.var (rightBinders rightDepth)) assignment index) [] signature.ids.object :=
      Assignment.extend_sorted signature context _ assignment (.var rightHead) assignmentSorted
    have leftBodyRead := encoded_body_read abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq rho names assignment assignmentEq leftBinders leftInjective leftAbove
      body leftDepth nodup namesAbove leftNames
    have rightBodyRead := encoded_body_read abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq rho names assignment assignmentEq rightBinders rightInjective rightAbove
      body rightDepth nodup namesAbove rightNames
    refine ⟨max 1 fuel + 2, ?_⟩
    simp only [alphaDisjoint, Mettapedia.Logic.HOL.rename]
    exact HOLKernelCongruenceReadback.existential_admitted signature abbreviation profile distinct dictionary parameters
      rules names antecedent (encodeType signature.symbol base domain) _ _ (leftBinders leftDepth) (rightBinders rightDepth)
      antecedentSorted (encodeType_sorted signature context base baseSorted domain) leftHead rightHead
      (encode_sorted signature context base constant leftBinders baseSorted constantSorted body _ (leftDepth + 1) leftExtendedSorted leftBodySlots)
      (encode_sorted signature context base constant rightBinders baseSorted constantSorted body _ (rightDepth + 1) rightExtendedSorted rightBodySlots)
      lambdaProof g (rename (Rename.lift rho) body) (rename (Rename.lift rho) body) contextRead (typeRead domain) (leftAbove leftDepth) (rightAbove rightDepth)
      leftBodyRead rightBodyRead ruleAt bindingAt (selected .applicationArgument) tree

theorem rebind_admitted (signature : Signature sorts terms)
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
    (base : Unit → Preterm) (constant : ∀ {type}, Const type → Preterm)
    (baseEq : base = fun _ => .var 0)
    (constantEq : ∀ {type} (symbol : Const type), constant symbol = .var (indices symbol))
    (binders temporary : Nat → Nat)
    (baseSorted : ∀ index, Preterm.HasType terms context (base index) [] signature.ids.type)
    (constantSorted : ∀ {type} (symbol : Const type),
      Preterm.HasType terms context (constant symbol) [] signature.ids.object)
    (bindersInjective : Function.Injective binders) (temporaryInjective : Function.Injective temporary)
    (bindersAbove : ∀ level, parameters ≤ binders level)
    (temporaryAbove : ∀ level, parameters ≤ temporary level)
    (baseIndependent : ∀ slot index, ¬ Preterm.HasVar context (binders slot) (base index))
    (temporaryIndependent : ∀ slot index, ¬ Preterm.HasVar context (temporary slot) (base index))
    {gamma : Ctx Unit} {type : Ty Unit} (source : Term Const gamma type)
    (assignment : Assignment gamma) (sourceDepth targetDepth temporaryDepth : Nat) (antecedent : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (assignmentSorted : ∀ {type} (index : Var gamma type),
      Preterm.HasType terms context (assignment index) [] signature.ids.object)
    (sourceSlots : ∀ offset < source.binderDepth,
      context[binders (sourceDepth + offset)]? = some (.bound signature.ids.object))
    (targetSlots : ∀ offset < source.binderDepth,
      context[binders (targetDepth + offset)]? = some (.bound signature.ids.object))
    (temporarySlots : ∀ offset < source.binderDepth,
      context[temporary (temporaryDepth + offset)]? = some (.bound signature.ids.object))
    (sourceFresh : ∀ offset < source.binderDepth,
      ¬ Preterm.HasVar context (binders (sourceDepth + offset)) antecedent)
    (targetFresh : ∀ offset < source.binderDepth,
      ¬ Preterm.HasVar context (binders (targetDepth + offset)) antecedent)
    (temporaryFresh : ∀ offset < source.binderDepth,
      ¬ Preterm.HasVar context (temporary (temporaryDepth + offset)) antecedent)
    (firstDisjoint : ∀ firstOffset < source.binderDepth, ∀ secondOffset < source.binderDepth,
      binders (sourceDepth + firstOffset) ≠ temporary (temporaryDepth + secondOffset))
    (secondDisjoint : ∀ firstOffset < source.binderDepth, ∀ secondOffset < source.binderDepth,
      temporary (temporaryDepth + firstOffset) ≠ binders (targetDepth + secondOffset))
    (variableTyping : ∀ {type} (index : Var gamma type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
        (context := context) (hypotheses := [])
        (typed signature.symbol antecedent (assignment index) (encodeType signature.symbol base type)))
    (constantTyping : ∀ {type} (symbol : Const type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
        (context := context) (hypotheses := [])
        (typed signature.symbol antecedent (constant symbol) (encodeType signature.symbol base type)))
    {delta : Ctx Unit} (rho : Rename Unit gamma delta) (names : Names delta)
    (nodup : names.toList.Nodup) (namesAbove : ∀ name ∈ names.toList, parameters ≤ name)
    (assignmentEq : ∀ {type} (index : Var gamma type), assignment index = .var (names.nameOf (rho index)))
    (sourceNames : ∀ offset < source.binderDepth, ∀ {type} (index : Var gamma type), binders (sourceDepth + offset) ≠ names.nameOf (rho index))
    (targetNames : ∀ offset < source.binderDepth, ∀ {type} (index : Var gamma type), binders (targetDepth + offset) ≠ names.nameOf (rho index))
    (temporaryNames : ∀ offset < source.binderDepth, ∀ {type} (index : Var gamma type), temporary (temporaryDepth + offset) ≠ names.nameOf (rho index))
    (g : Judgment Const delta)
    (contextRead : readJudgmentWith (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters)
      signature.symbol names (expandEquivalence signature.symbol abbreviation.reference antecedent) = some g)
    (ruleAt : Nat → Option HOLKernelRuleReadback.Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (selected : ∀ rule, ruleAt (rules.index rule) = some (.inference rule))
    (bindingSelected : bindingAt (binding.index .abstractionRenaming) = some .abstractionRenaming) :
    ∃ fuel, Nonempty (AdmittedProof abbreviation theorems context
      (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) parameters ruleAt bindingAt fuel names
      (rebind signature profile structural typing rules binding base constant binders temporary
        baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent source assignment
        sourceDepth targetDepth temporaryDepth antecedent antecedentSorted assignmentSorted
        sourceSlots targetSlots temporarySlots sourceFresh targetFresh temporaryFresh firstDisjoint secondDisjoint
        variableTyping constantTyping).val (.imp g.formula (.eq (rename rho source) (rename rho source)))) := by
  let first := alphaDisjoint signature profile structural typing rules binding base constant binders temporary
    baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent source assignment
    sourceDepth temporaryDepth antecedent antecedentSorted assignmentSorted sourceSlots temporarySlots sourceFresh temporaryFresh
    firstDisjoint variableTyping constantTyping
  let second := alphaDisjoint signature profile structural typing rules binding base constant temporary binders
    baseSorted constantSorted temporaryInjective bindersInjective temporaryIndependent baseIndependent source assignment
    temporaryDepth targetDepth antecedent antecedentSorted assignmentSorted temporarySlots targetSlots temporaryFresh targetFresh
    secondDisjoint variableTyping constantTyping
  obtain ⟨fuelFirst, ⟨firstTree⟩⟩ := alphaDisjoint_admitted signature abbreviation profile structural typing rules binding
    distinct dictionary indices parameters lookup bounded base constant baseEq constantEq binders temporary
    baseSorted constantSorted bindersInjective temporaryInjective bindersAbove temporaryAbove baseIndependent temporaryIndependent
    source assignment sourceDepth temporaryDepth antecedent antecedentSorted assignmentSorted sourceSlots temporarySlots
    sourceFresh temporaryFresh firstDisjoint variableTyping constantTyping rho names nodup namesAbove assignmentEq
    sourceNames temporaryNames g contextRead ruleAt bindingAt selected bindingSelected
  obtain ⟨fuelSecond, ⟨secondTree⟩⟩ := alphaDisjoint_admitted signature abbreviation profile structural typing rules binding
    distinct dictionary indices parameters lookup bounded base constant baseEq constantEq temporary binders
    baseSorted constantSorted temporaryInjective bindersInjective temporaryAbove bindersAbove temporaryIndependent baseIndependent
    source assignment temporaryDepth targetDepth antecedent antecedentSorted assignmentSorted temporarySlots targetSlots
    temporaryFresh targetFresh secondDisjoint variableTyping constantTyping rho names nodup namesAbove assignmentEq
    temporaryNames targetNames g contextRead ruleAt bindingAt selected bindingSelected
  have sourceRead := encoded_read abbreviation profile distinct dictionary indices parameters lookup bounded
    base constant baseEq constantEq rho names assignment assignmentEq binders bindersInjective bindersAbove
    source sourceDepth nodup namesAbove sourceNames
  have temporaryRead := encoded_read abbreviation profile distinct dictionary indices parameters lookup bounded
    base constant baseEq constantEq rho names assignment assignmentEq temporary temporaryInjective temporaryAbove
    source temporaryDepth nodup namesAbove temporaryNames
  have targetRead := encoded_read abbreviation profile distinct dictionary indices parameters lookup bounded
    base constant baseEq constantEq rho names assignment assignmentEq binders bindersInjective bindersAbove
    source targetDepth nodup namesAbove targetNames
  have typeRead : readType signature.symbol
      (expandEquivalence signature.symbol abbreviation.reference (encodeType signature.symbol base type)) = some type := by
    rw [baseEq, expandEquivalence_encodeType_of_fixed signature.symbol abbreviation.reference distinct
      (fun _ : Unit => .var 0) (fun _ => by simp [expandEquivalence])]
    exact readType_encode signature.symbol signature.symbol_injective type
  refine ⟨max fuelFirst fuelSecond + 1, ?_⟩
  exact HOLKernelCongruenceReadback.transitivity_admitted signature abbreviation profile distinct dictionary parameters
    rules names antecedent (encodeType signature.symbol base type) _ _ _ antecedentSorted
    (encodeType_sorted signature context base baseSorted type)
    (encode_sorted signature context base constant binders baseSorted constantSorted source assignment sourceDepth assignmentSorted sourceSlots)
    (encode_sorted signature context base constant temporary baseSorted constantSorted source assignment temporaryDepth assignmentSorted temporarySlots)
    (encode_sorted signature context base constant binders baseSorted constantSorted source assignment targetDepth assignmentSorted targetSlots)
    first second g (rename rho source) (rename rho source) (rename rho source) contextRead typeRead sourceRead temporaryRead targetRead
    ruleAt bindingAt (selected .transitivity) firstTree secondTree

#print axioms encoded_read_of_lookup
#print axioms encoded_read
#print axioms encoded_body_read
#print axioms alphaDisjoint_lambda_admitted
#print axioms alphaDisjoint_admitted
#print axioms rebind_admitted
/-- The actual three-window alpha receipt retains admission under lookup-preserving reader-frame maps. -/
theorem rebind_admission_under_renaming (signature : Signature sorts terms)
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
    (base : Unit → Preterm) (constant : ∀ {type}, Const type → Preterm)
    (baseEq : base = fun _ => .var 0)
    (constantEq : ∀ {type} (symbol : Const type), constant symbol = .var (indices symbol))
    (binders temporary : Nat → Nat)
    (baseSorted : ∀ index, Preterm.HasType terms context (base index) [] signature.ids.type)
    (constantSorted : ∀ {type} (symbol : Const type),
      Preterm.HasType terms context (constant symbol) [] signature.ids.object)
    (bindersInjective : Function.Injective binders) (temporaryInjective : Function.Injective temporary)
    (bindersAbove : ∀ level, parameters ≤ binders level)
    (temporaryAbove : ∀ level, parameters ≤ temporary level)
    (baseIndependent : ∀ slot index, ¬ Preterm.HasVar context (binders slot) (base index))
    (temporaryIndependent : ∀ slot index, ¬ Preterm.HasVar context (temporary slot) (base index))
    {gamma : Ctx Unit} {type : Ty Unit} (source : Term Const gamma type)
    (assignment : Assignment gamma) (sourceDepth targetDepth temporaryDepth : Nat) (antecedent : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (assignmentSorted : ∀ {type} (index : Var gamma type),
      Preterm.HasType terms context (assignment index) [] signature.ids.object)
    (sourceSlots : ∀ offset < source.binderDepth,
      context[binders (sourceDepth + offset)]? = some (.bound signature.ids.object))
    (targetSlots : ∀ offset < source.binderDepth,
      context[binders (targetDepth + offset)]? = some (.bound signature.ids.object))
    (temporarySlots : ∀ offset < source.binderDepth,
      context[temporary (temporaryDepth + offset)]? = some (.bound signature.ids.object))
    (sourceFresh : ∀ offset < source.binderDepth,
      ¬ Preterm.HasVar context (binders (sourceDepth + offset)) antecedent)
    (targetFresh : ∀ offset < source.binderDepth,
      ¬ Preterm.HasVar context (binders (targetDepth + offset)) antecedent)
    (temporaryFresh : ∀ offset < source.binderDepth,
      ¬ Preterm.HasVar context (temporary (temporaryDepth + offset)) antecedent)
    (firstDisjoint : ∀ firstOffset < source.binderDepth, ∀ secondOffset < source.binderDepth,
      binders (sourceDepth + firstOffset) ≠ temporary (temporaryDepth + secondOffset))
    (secondDisjoint : ∀ firstOffset < source.binderDepth, ∀ secondOffset < source.binderDepth,
      temporary (temporaryDepth + firstOffset) ≠ binders (targetDepth + secondOffset))
    (variableTyping : ∀ {type} (index : Var gamma type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
        (context := context) (hypotheses := [])
        (typed signature.symbol antecedent (assignment index) (encodeType signature.symbol base type)))
    (constantTyping : ∀ {type} (symbol : Const type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
        (context := context) (hypotheses := [])
        (typed signature.symbol antecedent (constant symbol) (encodeType signature.symbol base type)))
    {delta : Ctx Unit} (rho : Rename Unit gamma delta) (names : Names delta)
    (nodup : names.toList.Nodup)
    (assignmentEq : ∀ {type} (index : Var gamma type), assignment index = .var (names.nameOf (rho index)))
    (sourceNames : ∀ offset < source.binderDepth, ∀ {type} (index : Var gamma type), binders (sourceDepth + offset) ≠ names.nameOf (rho index))
    (targetNames : ∀ offset < source.binderDepth, ∀ {type} (index : Var gamma type), binders (targetDepth + offset) ≠ names.nameOf (rho index))
    (temporaryNames : ∀ offset < source.binderDepth, ∀ {type} (index : Var gamma type), temporary (temporaryDepth + offset) ≠ names.nameOf (rho index))
    (g : Judgment Const delta)
    (contextRead : readJudgmentWith (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters)
      signature.symbol names (expandEquivalence signature.symbol abbreviation.reference antecedent) = some g)
    (ruleAt : Nat → Option HOLKernelRuleReadback.Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (selected : ∀ rule, ruleAt (rules.index rule) = some (.inference rule))
    (bindingSelected : bindingAt (binding.index .abstractionRenaming) = some .abstractionRenaming) :
    AdmissionUnderRenaming (context := context) abbreviation profile dictionary parameters ruleAt bindingAt names
      (HOLKernelAlpha.rebind signature profile structural typing rules binding base constant binders temporary
        baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent source assignment
        sourceDepth targetDepth temporaryDepth antecedent antecedentSorted assignmentSorted
        sourceSlots targetSlots temporarySlots sourceFresh targetFresh temporaryFresh firstDisjoint secondDisjoint
        variableTyping constantTyping).val (.imp g.formula (.eq (rename rho source) (rename rho source))) := by
  intro target sigma future futureNodup futureAbove related
  let composed : Rename Unit gamma target := fun index => sigma (rho index)
  have futureAssignment : ∀ {type} (index : Var gamma type), assignment index = .var (future.nameOf (composed index)) := by
    intro type index
    simpa only [composed, related.nameOf nodup (rho index)] using assignmentEq index
  have futureContext := logical_judgment_rename_of_read profile dictionary parameters names future sigma related
    (expandEquivalence signature.symbol abbreviation.reference antecedent) g contextRead
  have result := HOLKernelAlphaReadback.rebind_admitted signature abbreviation profile structural typing rules binding
    distinct dictionary indices parameters lookup bounded base constant baseEq constantEq binders temporary
    baseSorted constantSorted bindersInjective temporaryInjective bindersAbove temporaryAbove baseIndependent temporaryIndependent
    source assignment sourceDepth targetDepth temporaryDepth antecedent antecedentSorted assignmentSorted
    sourceSlots targetSlots temporarySlots sourceFresh targetFresh temporaryFresh firstDisjoint secondDisjoint variableTyping constantTyping
    composed future futureNodup futureAbove futureAssignment
    (by intro offset less type index; simpa only [composed, related.nameOf nodup (rho index)] using sourceNames offset less index)
    (by intro offset less type index; simpa only [composed, related.nameOf nodup (rho index)] using targetNames offset less index)
    (by intro offset less type index; simpa only [composed, related.nameOf nodup (rho index)] using temporaryNames offset less index)
    (g.rename sigma) futureContext ruleAt bindingAt selected bindingSelected
  simpa only [Mettapedia.Logic.HOL.rename, Judgment.rename_formula, rename_comp, composed] using result

#print axioms rebind_admission_under_renaming
end Mettapedia.Languages.MM0.HOLKernelAlphaReadback
