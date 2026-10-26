import Mettapedia.Languages.MM0.HOLKernelTermAssignmentReadback
import Mettapedia.Languages.MM0.HOLKernelLogicalCongruenceReadback
import Mettapedia.Languages.MM0.HOLKernelStructuralReadback
import Mettapedia.Languages.MM0.HOLKernelTermCongruence

/-!
# Admission of native pointwise term-assignment congruence

The actual congruence producer preserves independently admitted equality
receipts through all thirteen HOL term constructors. Pointwise inputs carry
admission under lookup-preserving changes of reader frame. The binder case
extends their native equalities by reflexivity and structural weakening, then
uses native abstraction congruence. Lambda and both quantifiers share this
construction; the quantified cases add their existing logical adapters.

The endpoint readings are intrinsic simultaneous substitutions, not assumed
compound equalities. Native sorting, occurrence independence, fresh binders,
constant lookup and actual theorem selection remain explicit. Alpha rebinding
and structural assumption/weakening receipts have separate proved instances
of the contextual input property. The source-substitution producer composes
these results in `HOLKernelSubstitutionReadback`.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.MM0.HOLKernelTermCongruenceReadback
open Mettapedia.Logic Mettapedia.Logic.HOL
open Kernel HOLKernelSyntax HOLKernelTermAssignments HOLKernelJudgment
open HOLKernelTermReadback HOLKernelJudgmentReadback HOLKernelRuleReadback HOLKernelProofReadback
open HOLKernelTypeSupport
open HOLKernelTypingRules (typed boolType functionType)
open HOLKernelInferenceRules (equality)
open HOLKernelStructuralRules (CheckedProof)
open NamedElaboration (BinderNames)
universe u
variable {Const : Ty Unit → Type u}
variable {sorts : SortSignature} {terms : TermSignature} {definitions : Definition.Signature}
variable {theorems : TheoremSignature} {context : Context}

theorem assigned_read (signature : Signature sorts terms)
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (distinct : ∀ symbol, signature.symbol symbol ≠ abbreviation.reference)
    (dictionary : Nat → Option (NamedElaboration.SomeConst Const))
    (indices : ∀ {type}, Const type → Nat) (parameters : Nat)
    (lookup : ∀ {type} (symbol : Const type), dictionary (indices symbol) = some ⟨type, symbol⟩)
    (bounded : ∀ {type} (symbol : Const type), indices symbol < parameters)
    (base : Unit → Preterm) (constant : ∀ {type}, Const type → Preterm)
    (baseEq : base = fun _ => .var 0) (constantEq : ∀ {type} (symbol : Const type), constant symbol = .var (indices symbol))
    (binders : Nat → Nat) (injective : Function.Injective binders) (above : ∀ level, parameters ≤ binders level)
    {gamma delta : Ctx Unit} {type : Ty Unit} (source : Term Const gamma type)
    (meaning : Subst Const gamma delta) (assignment : Assignment gamma) (names : Names delta) (depth : Nat)
    (images : ∀ {type} (index : Var gamma type),
      HOLKernelLogicalFunctionReadback.reader profile dictionary parameters names (assignment index) = some ⟨type, meaning index⟩)
    (fixed : ∀ {type} (index : Var gamma type), expandEquivalence signature.symbol abbreviation.reference (assignment index) = assignment index)
    (constantsAbsent : ∀ {type} (symbol : Const type), names.lookup? (indices symbol) = none)
    (fresh : ∀ offset < source.binderDepth, names.lookup? (binders (depth + offset)) = none)
    (dictionaryFresh : ∀ offset < source.binderDepth, dictionary (binders (depth + offset)) = none) :
    HOLKernelLogicalFunctionReadback.reader profile dictionary parameters names
      (expandEquivalence signature.symbol abbreviation.reference
        (encodeWithAssignment signature.symbol base constant binders assignment depth source)) =
      some ⟨type, HOL.subst meaning source⟩ := by
  rw [expandEquivalence_encodeWithAssignment_of_fixed signature.symbol abbreviation.reference distinct base constant binders
    (fun name => by simp [baseEq, expandEquivalence]) (fun symbol => by simp [constantEq, expandEquivalence]) source assignment depth fixed]
  have constantsEq : (fun {type} (symbol : Const type) => constant symbol) =
      (fun {type} (symbol : Const type) => Preterm.var (indices symbol)) := by
    funext type symbol
    exact constantEq symbol
  rw [baseEq, constantsEq]
  exact readTermWith_encodeWithAssignment (HOLKernelLogicalFunctionReadback.atoms profile)
    (fun rho term => logical_atoms_rename profile rho term) signature.symbol signature.symbol_injective dictionary indices parameters
    lookup bounded binders injective above source meaning assignment names depth images constantsAbsent fresh dictionaryFresh

theorem congruence_admitted (signature : Signature sorts terms)
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
    (baseEq : base = fun _ => .var 0) (constantEq : ∀ {type} (symbol : Const type), constant symbol = .var (indices symbol))
    (binders : Nat → Nat)
    (baseSorted : ∀ index, Preterm.HasType terms context (base index) [] signature.ids.type)
    (constantSorted : ∀ {type} (symbol : Const type), Preterm.HasType terms context (constant symbol) [] signature.ids.object)
    (injective : Function.Injective binders) (above : ∀ level, parameters ≤ binders level)
    (baseIndependent : ∀ slot index, ¬ Preterm.HasVar context (binders slot) (base index))
    {gamma : Ctx Unit} {type : Ty Unit} (source : Term Const gamma type) :
    ∀ (left right : Assignment gamma) (depth : Nat) (antecedent : Preterm)
      (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
      (leftSorted : ∀ {type} (index : Var gamma type), Preterm.HasType terms context (left index) [] signature.ids.object)
      (rightSorted : ∀ {type} (index : Var gamma type), Preterm.HasType terms context (right index) [] signature.ids.object)
      (slots : ∀ offset < source.binderDepth, context[binders (depth + offset)]? = some (.bound signature.ids.object))
      (independent : ∀ offset < source.binderDepth, ¬ Preterm.HasVar context (binders (depth + offset)) antecedent)
      (variableEquality : ∀ {type} (index : Var gamma type),
        CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems) (context := context) (hypotheses := [])
          (entails signature.symbol antecedent (holds signature.symbol
            (equality signature.symbol (encodeType signature.symbol base type) (left index) (right index)))))
      (constantTyping : ∀ {type} (symbol : Const type),
        CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems) (context := context) (hypotheses := [])
          (typed signature.symbol antecedent (constant symbol) (encodeType signature.symbol base type)))
      {delta : Ctx Unit} (leftMeaning rightMeaning : Subst Const gamma delta) (names : Names delta)
      (_ : names.toList.Nodup) (_ : ∀ name ∈ names.toList, parameters ≤ name)
      (_ : ∀ {type} (index : Var gamma type), HOLKernelLogicalFunctionReadback.reader profile dictionary parameters names (left index) = some ⟨type, leftMeaning index⟩)
      (_ : ∀ {type} (index : Var gamma type), HOLKernelLogicalFunctionReadback.reader profile dictionary parameters names (right index) = some ⟨type, rightMeaning index⟩)
      (_ : ∀ {type} (index : Var gamma type), expandEquivalence signature.symbol abbreviation.reference (left index) = left index)
      (_ : ∀ {type} (index : Var gamma type), expandEquivalence signature.symbol abbreviation.reference (right index) = right index)
      (_ : ∀ {type} (symbol : Const type), names.lookup? (indices symbol) = none)
      (_ : ∀ offset < source.binderDepth, names.lookup? (binders (depth + offset)) = none)
      (_ : ∀ offset < source.binderDepth, dictionary (binders (depth + offset)) = none)
      (g : Judgment Const delta)
      (_ : readJudgmentWith (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) signature.symbol names
        (expandEquivalence signature.symbol abbreviation.reference antecedent) = some g)
      (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
      (_ : ∀ rule, ruleAt (rules.index rule) = some (.inference rule))
      (_ : ∀ rule, ruleAt (structural.index rule) = some (.structural rule))
      (_ : bindingAt (binding.index .abstractionCongruence) = some .abstractionCongruence)
      (_ : ∀ {type} (index : Var gamma type), AdmissionUnderRenaming (context := context) abbreviation profile dictionary parameters
        ruleAt bindingAt names (variableEquality index).val (.imp g.formula (.eq (leftMeaning index) (rightMeaning index)))),
      ∃ fuel, Nonempty (AdmittedProof abbreviation theorems context
        (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) parameters ruleAt bindingAt fuel names
        (HOLKernelTermCongruence.congruence signature profile structural typing rules binding base constant binders
          baseSorted constantSorted injective baseIndependent source left right depth antecedent antecedentSorted
          leftSorted rightSorted slots independent variableEquality constantTyping).val
        (.imp g.formula (.eq (HOL.subst leftMeaning source) (HOL.subst rightMeaning source)))) := by
  have typeRead (type : Ty Unit) : readType signature.symbol
      (expandEquivalence signature.symbol abbreviation.reference (encodeType signature.symbol base type)) = some type := by
    rw [baseEq, expandEquivalence_encodeType_of_fixed signature.symbol abbreviation.reference distinct
      (fun _ : Unit => .var 0) (fun _ => by simp [expandEquivalence])]
    exact readType_encode signature.symbol signature.symbol_injective type
  induction source with
  | var index =>
    intro left right depth antecedent antecedentSorted leftSorted rightSorted slots independent variableEquality constantTyping
      delta leftMeaning rightMeaning names nodup namesAbove leftRead rightRead leftFixed rightFixed constantsAbsent
      fresh dictionaryFresh g contextRead ruleAt bindingAt selected structuralSelected bindingSelected variableAdmitted
    simpa only [HOLKernelTermCongruence.congruence, HOL.subst] using
      AdmissionUnderRenaming.at_identity (variableAdmitted index) nodup namesAbove
  | const symbol =>
    intro left right depth antecedent antecedentSorted leftSorted rightSorted slots independent variableEquality constantTyping
      delta leftMeaning rightMeaning names nodup namesAbove leftRead rightRead leftFixed rightFixed constantsAbsent
      fresh dictionaryFresh g contextRead ruleAt bindingAt selected structuralSelected bindingSelected variableAdmitted
    have reading := assigned_read signature abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq binders injective above (Term.const symbol) leftMeaning left names depth leftRead leftFixed constantsAbsent fresh dictionaryFresh
    refine ⟨2, ?_⟩
    simpa only [HOLKernelTermCongruence.congruence, encodeWithAssignment, HOL.subst, encodeType] using
      HOLKernelCongruenceReadback.reflexivity_admitted signature abbreviation profile distinct dictionary parameters
        rules names antecedent (encodeType signature.symbol base _) (constant symbol) antecedentSorted
        (encodeType_sorted signature context base baseSorted _) (constantSorted symbol) (constantTyping symbol)
        g (Term.const symbol) contextRead (typeRead _) reading ruleAt bindingAt (selected .reflexivity)
  | top =>
    intro left right depth antecedent antecedentSorted leftSorted rightSorted slots independent variableEquality constantTyping
      delta leftMeaning rightMeaning names nodup namesAbove leftRead rightRead leftFixed rightFixed constantsAbsent
      fresh dictionaryFresh g contextRead ruleAt bindingAt selected structuralSelected bindingSelected variableAdmitted
    have reading := assigned_read signature abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq binders injective above (Term.top : Formula Const _) leftMeaning left names depth leftRead leftFixed constantsAbsent fresh dictionaryFresh
    refine ⟨2, ?_⟩
    simpa only [HOLKernelTermCongruence.congruence, encodeWithAssignment, HOL.subst, encodeType] using
      HOLKernelCongruenceReadback.reflexivity_admitted signature abbreviation profile distinct dictionary parameters
        rules names antecedent (encodeType signature.symbol base .prop) (applySymbol signature.symbol .truth []) antecedentSorted
        (encodeType_sorted signature context base baseSorted .prop) (signature.application context .truth [] .nil) (HOLKernelTypingProofs.truthTyping signature typing antecedent antecedentSorted)
        g (Term.top : Formula Const _) contextRead (typeRead _) reading ruleAt bindingAt (selected .reflexivity)
  | bot =>
    intro left right depth antecedent antecedentSorted leftSorted rightSorted slots independent variableEquality constantTyping
      delta leftMeaning rightMeaning names nodup namesAbove leftRead rightRead leftFixed rightFixed constantsAbsent
      fresh dictionaryFresh g contextRead ruleAt bindingAt selected structuralSelected bindingSelected variableAdmitted
    have reading := assigned_read signature abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq binders injective above (Term.bot : Formula Const _) leftMeaning left names depth leftRead leftFixed constantsAbsent fresh dictionaryFresh
    refine ⟨2, ?_⟩
    simpa only [HOLKernelTermCongruence.congruence, encodeWithAssignment, HOL.subst, encodeType] using
      HOLKernelCongruenceReadback.reflexivity_admitted signature abbreviation profile distinct dictionary parameters
        rules names antecedent (encodeType signature.symbol base .prop) (applySymbol signature.symbol .falsity []) antecedentSorted
        (encodeType_sorted signature context base baseSorted .prop) (signature.application context .falsity [] .nil) (HOLKernelTypingProofs.falsityTyping signature typing antecedent antecedentSorted)
        g (Term.bot : Formula Const _) contextRead (typeRead _) reading ruleAt bindingAt (selected .reflexivity)
  | @app gamma domain result first second ihFirst ihSecond =>
    intro left right depth antecedent antecedentSorted leftSorted rightSorted slots independent variableEquality constantTyping
      delta leftMeaning rightMeaning names nodup namesAbove leftRead rightRead leftFixed rightFixed constantsAbsent
      fresh dictionaryFresh g contextRead ruleAt bindingAt selected structuralSelected bindingSelected variableAdmitted
    have firstSlots := fun offset smaller => slots offset
      (Nat.lt_of_lt_of_le smaller (Nat.le_max_left first.binderDepth second.binderDepth))
    have secondSlots := fun offset smaller => slots offset
      (Nat.lt_of_lt_of_le smaller (Nat.le_max_right first.binderDepth second.binderDepth))
    have firstIndependent := fun offset smaller => independent offset
      (Nat.lt_of_lt_of_le smaller (Nat.le_max_left first.binderDepth second.binderDepth))
    have secondIndependent := fun offset smaller => independent offset
      (Nat.lt_of_lt_of_le smaller (Nat.le_max_right first.binderDepth second.binderDepth))
    have leftFirstSorted := encode_sorted signature context base constant binders baseSorted
      constantSorted first left depth leftSorted firstSlots
    have rightFirstSorted := encode_sorted signature context base constant binders baseSorted
      constantSorted first right depth rightSorted firstSlots
    have leftSecondSorted := encode_sorted signature context base constant binders baseSorted
      constantSorted second left depth leftSorted secondSlots
    have rightSecondSorted := encode_sorted signature context base constant binders baseSorted
      constantSorted second right depth rightSorted secondSlots
    let firstProof := HOLKernelTermCongruence.congruence signature profile structural typing rules binding base constant binders
      baseSorted constantSorted injective baseIndependent first left right depth antecedent
      antecedentSorted leftSorted rightSorted firstSlots firstIndependent variableEquality constantTyping
    let secondProof := HOLKernelTermCongruence.congruence signature profile structural typing rules binding base constant binders
      baseSorted constantSorted injective baseIndependent second left right depth antecedent
      antecedentSorted leftSorted rightSorted secondSlots secondIndependent variableEquality constantTyping
    have firstFresh := fun offset less => fresh offset (Nat.lt_of_lt_of_le less (Nat.le_max_left _ _))
    have firstDictionary := fun offset less => dictionaryFresh offset (Nat.lt_of_lt_of_le less (Nat.le_max_left _ _))
    obtain ⟨fuelFirst, ⟨treeFirst⟩⟩ := ihFirst left right depth antecedent antecedentSorted leftSorted rightSorted
      firstSlots firstIndependent variableEquality constantTyping leftMeaning rightMeaning names nodup namesAbove
      leftRead rightRead leftFixed rightFixed constantsAbsent firstFresh firstDictionary g contextRead
      ruleAt bindingAt selected structuralSelected bindingSelected variableAdmitted
    have leftFirstRead := assigned_read signature abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq binders injective above first leftMeaning left names depth leftRead leftFixed constantsAbsent firstFresh firstDictionary
    have rightFirstRead := assigned_read signature abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq binders injective above first rightMeaning right names depth rightRead rightFixed constantsAbsent firstFresh firstDictionary
    have secondFresh := fun offset less => fresh offset (Nat.lt_of_lt_of_le less (Nat.le_max_right _ _))
    have secondDictionary := fun offset less => dictionaryFresh offset (Nat.lt_of_lt_of_le less (Nat.le_max_right _ _))
    obtain ⟨fuelSecond, ⟨treeSecond⟩⟩ := ihSecond left right depth antecedent antecedentSorted leftSorted rightSorted
      secondSlots secondIndependent variableEquality constantTyping leftMeaning rightMeaning names nodup namesAbove
      leftRead rightRead leftFixed rightFixed constantsAbsent secondFresh secondDictionary g contextRead
      ruleAt bindingAt selected structuralSelected bindingSelected variableAdmitted
    have leftSecondRead := assigned_read signature abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq binders injective above second leftMeaning left names depth leftRead leftFixed constantsAbsent secondFresh secondDictionary
    have rightSecondRead := assigned_read signature abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq binders injective above second rightMeaning right names depth rightRead rightFixed constantsAbsent secondFresh secondDictionary
    simpa only [HOLKernelTermCongruence.congruence, HOL.subst] using
      HOLKernelCongruenceReadback.application_admitted signature abbreviation profile distinct dictionary parameters
        rules binding names antecedent (encodeType signature.symbol base domain) (encodeType signature.symbol base result) _ _ _ _
        antecedentSorted (encodeType_sorted signature context base baseSorted domain) (encodeType_sorted signature context base baseSorted result)
        leftFirstSorted rightFirstSorted leftSecondSorted rightSecondSorted firstProof secondProof g
        (HOL.subst leftMeaning first) (HOL.subst rightMeaning first) (HOL.subst leftMeaning second) (HOL.subst rightMeaning second)
        contextRead (typeRead domain) (typeRead result) leftFirstRead rightFirstRead leftSecondRead rightSecondRead
        ruleAt bindingAt selected treeFirst treeSecond
  | @and gamma first second ihFirst ihSecond =>
    intro left right depth antecedent antecedentSorted leftSorted rightSorted slots independent variableEquality constantTyping
      delta leftMeaning rightMeaning names nodup namesAbove leftRead rightRead leftFixed rightFixed constantsAbsent
      fresh dictionaryFresh g contextRead ruleAt bindingAt selected structuralSelected bindingSelected variableAdmitted
    have firstSlots := fun offset smaller => slots offset
      (Nat.lt_of_lt_of_le smaller (Nat.le_max_left first.binderDepth second.binderDepth))
    have secondSlots := fun offset smaller => slots offset
      (Nat.lt_of_lt_of_le smaller (Nat.le_max_right first.binderDepth second.binderDepth))
    have firstIndependent := fun offset smaller => independent offset
      (Nat.lt_of_lt_of_le smaller (Nat.le_max_left first.binderDepth second.binderDepth))
    have secondIndependent := fun offset smaller => independent offset
      (Nat.lt_of_lt_of_le smaller (Nat.le_max_right first.binderDepth second.binderDepth))
    have leftFirstSorted := encode_sorted signature context base constant binders baseSorted
      constantSorted first left depth leftSorted firstSlots
    have rightFirstSorted := encode_sorted signature context base constant binders baseSorted
      constantSorted first right depth rightSorted firstSlots
    have leftSecondSorted := encode_sorted signature context base constant binders baseSorted
      constantSorted second left depth leftSorted secondSlots
    have rightSecondSorted := encode_sorted signature context base constant binders baseSorted
      constantSorted second right depth rightSorted secondSlots
    let firstProof := HOLKernelTermCongruence.congruence signature profile structural typing rules binding base constant binders
      baseSorted constantSorted injective baseIndependent first left right depth antecedent
      antecedentSorted leftSorted rightSorted firstSlots firstIndependent variableEquality constantTyping
    let secondProof := HOLKernelTermCongruence.congruence signature profile structural typing rules binding base constant binders
      baseSorted constantSorted injective baseIndependent second left right depth antecedent
      antecedentSorted leftSorted rightSorted secondSlots secondIndependent variableEquality constantTyping
    have firstFresh := fun offset less => fresh offset (Nat.lt_of_lt_of_le less (Nat.le_max_left _ _))
    have firstDictionary := fun offset less => dictionaryFresh offset (Nat.lt_of_lt_of_le less (Nat.le_max_left _ _))
    obtain ⟨fuelFirst, ⟨treeFirst⟩⟩ := ihFirst left right depth antecedent antecedentSorted leftSorted rightSorted
      firstSlots firstIndependent variableEquality constantTyping leftMeaning rightMeaning names nodup namesAbove
      leftRead rightRead leftFixed rightFixed constantsAbsent firstFresh firstDictionary g contextRead
      ruleAt bindingAt selected structuralSelected bindingSelected variableAdmitted
    have leftFirstRead := assigned_read signature abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq binders injective above first leftMeaning left names depth leftRead leftFixed constantsAbsent firstFresh firstDictionary
    have rightFirstRead := assigned_read signature abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq binders injective above first rightMeaning right names depth rightRead rightFixed constantsAbsent firstFresh firstDictionary
    have secondFresh := fun offset less => fresh offset (Nat.lt_of_lt_of_le less (Nat.le_max_right _ _))
    have secondDictionary := fun offset less => dictionaryFresh offset (Nat.lt_of_lt_of_le less (Nat.le_max_right _ _))
    obtain ⟨fuelSecond, ⟨treeSecond⟩⟩ := ihSecond left right depth antecedent antecedentSorted leftSorted rightSorted
      secondSlots secondIndependent variableEquality constantTyping leftMeaning rightMeaning names nodup namesAbove
      leftRead rightRead leftFixed rightFixed constantsAbsent secondFresh secondDictionary g contextRead
      ruleAt bindingAt selected structuralSelected bindingSelected variableAdmitted
    have leftSecondRead := assigned_read signature abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq binders injective above second leftMeaning left names depth leftRead leftFixed constantsAbsent secondFresh secondDictionary
    have rightSecondRead := assigned_read signature abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq binders injective above second rightMeaning right names depth rightRead rightFixed constantsAbsent secondFresh secondDictionary
    simpa only [HOLKernelTermCongruence.congruence, HOL.subst] using
      HOLKernelCongruenceReadback.conjunction_admitted signature abbreviation profile distinct dictionary parameters
        rules binding names antecedent _ _ _ _ antecedentSorted leftFirstSorted rightFirstSorted leftSecondSorted rightSecondSorted
        firstProof secondProof g (HOL.subst leftMeaning first) (HOL.subst rightMeaning first)
        (HOL.subst leftMeaning second) (HOL.subst rightMeaning second) contextRead
        leftFirstRead rightFirstRead leftSecondRead rightSecondRead ruleAt bindingAt selected treeFirst treeSecond
  | @or gamma first second ihFirst ihSecond =>
    intro left right depth antecedent antecedentSorted leftSorted rightSorted slots independent variableEquality constantTyping
      delta leftMeaning rightMeaning names nodup namesAbove leftRead rightRead leftFixed rightFixed constantsAbsent
      fresh dictionaryFresh g contextRead ruleAt bindingAt selected structuralSelected bindingSelected variableAdmitted
    have firstSlots := fun offset smaller => slots offset
      (Nat.lt_of_lt_of_le smaller (Nat.le_max_left first.binderDepth second.binderDepth))
    have secondSlots := fun offset smaller => slots offset
      (Nat.lt_of_lt_of_le smaller (Nat.le_max_right first.binderDepth second.binderDepth))
    have firstIndependent := fun offset smaller => independent offset
      (Nat.lt_of_lt_of_le smaller (Nat.le_max_left first.binderDepth second.binderDepth))
    have secondIndependent := fun offset smaller => independent offset
      (Nat.lt_of_lt_of_le smaller (Nat.le_max_right first.binderDepth second.binderDepth))
    have leftFirstSorted := encode_sorted signature context base constant binders baseSorted
      constantSorted first left depth leftSorted firstSlots
    have rightFirstSorted := encode_sorted signature context base constant binders baseSorted
      constantSorted first right depth rightSorted firstSlots
    have leftSecondSorted := encode_sorted signature context base constant binders baseSorted
      constantSorted second left depth leftSorted secondSlots
    have rightSecondSorted := encode_sorted signature context base constant binders baseSorted
      constantSorted second right depth rightSorted secondSlots
    let firstProof := HOLKernelTermCongruence.congruence signature profile structural typing rules binding base constant binders
      baseSorted constantSorted injective baseIndependent first left right depth antecedent
      antecedentSorted leftSorted rightSorted firstSlots firstIndependent variableEquality constantTyping
    let secondProof := HOLKernelTermCongruence.congruence signature profile structural typing rules binding base constant binders
      baseSorted constantSorted injective baseIndependent second left right depth antecedent
      antecedentSorted leftSorted rightSorted secondSlots secondIndependent variableEquality constantTyping
    have firstFresh := fun offset less => fresh offset (Nat.lt_of_lt_of_le less (Nat.le_max_left _ _))
    have firstDictionary := fun offset less => dictionaryFresh offset (Nat.lt_of_lt_of_le less (Nat.le_max_left _ _))
    obtain ⟨fuelFirst, ⟨treeFirst⟩⟩ := ihFirst left right depth antecedent antecedentSorted leftSorted rightSorted
      firstSlots firstIndependent variableEquality constantTyping leftMeaning rightMeaning names nodup namesAbove
      leftRead rightRead leftFixed rightFixed constantsAbsent firstFresh firstDictionary g contextRead
      ruleAt bindingAt selected structuralSelected bindingSelected variableAdmitted
    have leftFirstRead := assigned_read signature abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq binders injective above first leftMeaning left names depth leftRead leftFixed constantsAbsent firstFresh firstDictionary
    have rightFirstRead := assigned_read signature abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq binders injective above first rightMeaning right names depth rightRead rightFixed constantsAbsent firstFresh firstDictionary
    have secondFresh := fun offset less => fresh offset (Nat.lt_of_lt_of_le less (Nat.le_max_right _ _))
    have secondDictionary := fun offset less => dictionaryFresh offset (Nat.lt_of_lt_of_le less (Nat.le_max_right _ _))
    obtain ⟨fuelSecond, ⟨treeSecond⟩⟩ := ihSecond left right depth antecedent antecedentSorted leftSorted rightSorted
      secondSlots secondIndependent variableEquality constantTyping leftMeaning rightMeaning names nodup namesAbove
      leftRead rightRead leftFixed rightFixed constantsAbsent secondFresh secondDictionary g contextRead
      ruleAt bindingAt selected structuralSelected bindingSelected variableAdmitted
    have leftSecondRead := assigned_read signature abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq binders injective above second leftMeaning left names depth leftRead leftFixed constantsAbsent secondFresh secondDictionary
    have rightSecondRead := assigned_read signature abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq binders injective above second rightMeaning right names depth rightRead rightFixed constantsAbsent secondFresh secondDictionary
    simpa only [HOLKernelTermCongruence.congruence, HOL.subst] using
      HOLKernelCongruenceReadback.disjunction_admitted signature abbreviation profile distinct dictionary parameters
        rules binding names antecedent _ _ _ _ antecedentSorted leftFirstSorted rightFirstSorted leftSecondSorted rightSecondSorted
        firstProof secondProof g (HOL.subst leftMeaning first) (HOL.subst rightMeaning first)
        (HOL.subst leftMeaning second) (HOL.subst rightMeaning second) contextRead
        leftFirstRead rightFirstRead leftSecondRead rightSecondRead ruleAt bindingAt selected treeFirst treeSecond
  | @imp gamma first second ihFirst ihSecond =>
    intro left right depth antecedent antecedentSorted leftSorted rightSorted slots independent variableEquality constantTyping
      delta leftMeaning rightMeaning names nodup namesAbove leftRead rightRead leftFixed rightFixed constantsAbsent
      fresh dictionaryFresh g contextRead ruleAt bindingAt selected structuralSelected bindingSelected variableAdmitted
    have firstSlots := fun offset smaller => slots offset
      (Nat.lt_of_lt_of_le smaller (Nat.le_max_left first.binderDepth second.binderDepth))
    have secondSlots := fun offset smaller => slots offset
      (Nat.lt_of_lt_of_le smaller (Nat.le_max_right first.binderDepth second.binderDepth))
    have firstIndependent := fun offset smaller => independent offset
      (Nat.lt_of_lt_of_le smaller (Nat.le_max_left first.binderDepth second.binderDepth))
    have secondIndependent := fun offset smaller => independent offset
      (Nat.lt_of_lt_of_le smaller (Nat.le_max_right first.binderDepth second.binderDepth))
    have leftFirstSorted := encode_sorted signature context base constant binders baseSorted
      constantSorted first left depth leftSorted firstSlots
    have rightFirstSorted := encode_sorted signature context base constant binders baseSorted
      constantSorted first right depth rightSorted firstSlots
    have leftSecondSorted := encode_sorted signature context base constant binders baseSorted
      constantSorted second left depth leftSorted secondSlots
    have rightSecondSorted := encode_sorted signature context base constant binders baseSorted
      constantSorted second right depth rightSorted secondSlots
    let firstProof := HOLKernelTermCongruence.congruence signature profile structural typing rules binding base constant binders
      baseSorted constantSorted injective baseIndependent first left right depth antecedent
      antecedentSorted leftSorted rightSorted firstSlots firstIndependent variableEquality constantTyping
    let secondProof := HOLKernelTermCongruence.congruence signature profile structural typing rules binding base constant binders
      baseSorted constantSorted injective baseIndependent second left right depth antecedent
      antecedentSorted leftSorted rightSorted secondSlots secondIndependent variableEquality constantTyping
    have firstFresh := fun offset less => fresh offset (Nat.lt_of_lt_of_le less (Nat.le_max_left _ _))
    have firstDictionary := fun offset less => dictionaryFresh offset (Nat.lt_of_lt_of_le less (Nat.le_max_left _ _))
    obtain ⟨fuelFirst, ⟨treeFirst⟩⟩ := ihFirst left right depth antecedent antecedentSorted leftSorted rightSorted
      firstSlots firstIndependent variableEquality constantTyping leftMeaning rightMeaning names nodup namesAbove
      leftRead rightRead leftFixed rightFixed constantsAbsent firstFresh firstDictionary g contextRead
      ruleAt bindingAt selected structuralSelected bindingSelected variableAdmitted
    have leftFirstRead := assigned_read signature abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq binders injective above first leftMeaning left names depth leftRead leftFixed constantsAbsent firstFresh firstDictionary
    have rightFirstRead := assigned_read signature abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq binders injective above first rightMeaning right names depth rightRead rightFixed constantsAbsent firstFresh firstDictionary
    have secondFresh := fun offset less => fresh offset (Nat.lt_of_lt_of_le less (Nat.le_max_right _ _))
    have secondDictionary := fun offset less => dictionaryFresh offset (Nat.lt_of_lt_of_le less (Nat.le_max_right _ _))
    obtain ⟨fuelSecond, ⟨treeSecond⟩⟩ := ihSecond left right depth antecedent antecedentSorted leftSorted rightSorted
      secondSlots secondIndependent variableEquality constantTyping leftMeaning rightMeaning names nodup namesAbove
      leftRead rightRead leftFixed rightFixed constantsAbsent secondFresh secondDictionary g contextRead
      ruleAt bindingAt selected structuralSelected bindingSelected variableAdmitted
    have leftSecondRead := assigned_read signature abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq binders injective above second leftMeaning left names depth leftRead leftFixed constantsAbsent secondFresh secondDictionary
    have rightSecondRead := assigned_read signature abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq binders injective above second rightMeaning right names depth rightRead rightFixed constantsAbsent secondFresh secondDictionary
    simpa only [HOLKernelTermCongruence.congruence, HOL.subst] using
      HOLKernelCongruenceReadback.implication_admitted signature abbreviation profile distinct dictionary parameters
        rules binding names antecedent _ _ _ _ antecedentSorted leftFirstSorted rightFirstSorted leftSecondSorted rightSecondSorted
        firstProof secondProof g (HOL.subst leftMeaning first) (HOL.subst rightMeaning first)
        (HOL.subst leftMeaning second) (HOL.subst rightMeaning second) contextRead
        leftFirstRead rightFirstRead leftSecondRead rightSecondRead ruleAt bindingAt selected treeFirst treeSecond
  | @not gamma body ih =>
    intro left right depth antecedent antecedentSorted leftSorted rightSorted slots independent variableEquality constantTyping
      delta leftMeaning rightMeaning names nodup namesAbove leftRead rightRead leftFixed rightFixed constantsAbsent
      fresh dictionaryFresh g contextRead ruleAt bindingAt selected structuralSelected bindingSelected variableAdmitted
    let child := HOLKernelTermCongruence.congruence signature profile structural typing rules binding base constant binders
      baseSorted constantSorted injective baseIndependent body left right depth antecedent antecedentSorted leftSorted rightSorted
      slots independent variableEquality constantTyping
    obtain ⟨fuel, ⟨tree⟩⟩ := ih left right depth antecedent antecedentSorted leftSorted rightSorted slots independent variableEquality constantTyping
      leftMeaning rightMeaning names nodup namesAbove leftRead rightRead leftFixed rightFixed constantsAbsent fresh dictionaryFresh
      g contextRead ruleAt bindingAt selected structuralSelected bindingSelected variableAdmitted
    have leftBodyRead := assigned_read signature abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq binders injective above body leftMeaning left names depth leftRead leftFixed constantsAbsent fresh dictionaryFresh
    have rightBodyRead := assigned_read signature abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq binders injective above body rightMeaning right names depth rightRead rightFixed constantsAbsent fresh dictionaryFresh
    refine ⟨max 1 fuel + 2, ?_⟩
    simpa only [HOLKernelTermCongruence.congruence, HOL.subst] using
      HOLKernelCongruenceReadback.negation_admitted signature abbreviation profile distinct dictionary parameters rules names antecedent _ _
        antecedentSorted
        (encode_sorted signature context base constant binders baseSorted constantSorted body left depth leftSorted slots)
        (encode_sorted signature context base constant binders baseSorted constantSorted body right depth rightSorted slots)
        child g (HOL.subst leftMeaning body) (HOL.subst rightMeaning body) contextRead leftBodyRead rightBodyRead
        ruleAt bindingAt (selected .applicationArgument) tree
  | @eq gamma operand first second ihFirst ihSecond =>
    intro left right depth antecedent antecedentSorted leftSorted rightSorted slots independent variableEquality constantTyping
      delta leftMeaning rightMeaning names nodup namesAbove leftRead rightRead leftFixed rightFixed constantsAbsent
      fresh dictionaryFresh g contextRead ruleAt bindingAt selected structuralSelected bindingSelected variableAdmitted
    have firstSlots := fun offset smaller => slots offset
      (Nat.lt_of_lt_of_le smaller (Nat.le_max_left first.binderDepth second.binderDepth))
    have secondSlots := fun offset smaller => slots offset
      (Nat.lt_of_lt_of_le smaller (Nat.le_max_right first.binderDepth second.binderDepth))
    have firstIndependent := fun offset smaller => independent offset
      (Nat.lt_of_lt_of_le smaller (Nat.le_max_left first.binderDepth second.binderDepth))
    have secondIndependent := fun offset smaller => independent offset
      (Nat.lt_of_lt_of_le smaller (Nat.le_max_right first.binderDepth second.binderDepth))
    have leftFirstSorted := encode_sorted signature context base constant binders baseSorted
      constantSorted first left depth leftSorted firstSlots
    have rightFirstSorted := encode_sorted signature context base constant binders baseSorted
      constantSorted first right depth rightSorted firstSlots
    have leftSecondSorted := encode_sorted signature context base constant binders baseSorted
      constantSorted second left depth leftSorted secondSlots
    have rightSecondSorted := encode_sorted signature context base constant binders baseSorted
      constantSorted second right depth rightSorted secondSlots
    let firstProof := HOLKernelTermCongruence.congruence signature profile structural typing rules binding base constant binders
      baseSorted constantSorted injective baseIndependent first left right depth antecedent
      antecedentSorted leftSorted rightSorted firstSlots firstIndependent variableEquality constantTyping
    let secondProof := HOLKernelTermCongruence.congruence signature profile structural typing rules binding base constant binders
      baseSorted constantSorted injective baseIndependent second left right depth antecedent
      antecedentSorted leftSorted rightSorted secondSlots secondIndependent variableEquality constantTyping
    have firstFresh := fun offset less => fresh offset (Nat.lt_of_lt_of_le less (Nat.le_max_left _ _))
    have firstDictionary := fun offset less => dictionaryFresh offset (Nat.lt_of_lt_of_le less (Nat.le_max_left _ _))
    obtain ⟨fuelFirst, ⟨treeFirst⟩⟩ := ihFirst left right depth antecedent antecedentSorted leftSorted rightSorted
      firstSlots firstIndependent variableEquality constantTyping leftMeaning rightMeaning names nodup namesAbove
      leftRead rightRead leftFixed rightFixed constantsAbsent firstFresh firstDictionary g contextRead
      ruleAt bindingAt selected structuralSelected bindingSelected variableAdmitted
    have leftFirstRead := assigned_read signature abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq binders injective above first leftMeaning left names depth leftRead leftFixed constantsAbsent firstFresh firstDictionary
    have rightFirstRead := assigned_read signature abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq binders injective above first rightMeaning right names depth rightRead rightFixed constantsAbsent firstFresh firstDictionary
    have secondFresh := fun offset less => fresh offset (Nat.lt_of_lt_of_le less (Nat.le_max_right _ _))
    have secondDictionary := fun offset less => dictionaryFresh offset (Nat.lt_of_lt_of_le less (Nat.le_max_right _ _))
    obtain ⟨fuelSecond, ⟨treeSecond⟩⟩ := ihSecond left right depth antecedent antecedentSorted leftSorted rightSorted
      secondSlots secondIndependent variableEquality constantTyping leftMeaning rightMeaning names nodup namesAbove
      leftRead rightRead leftFixed rightFixed constantsAbsent secondFresh secondDictionary g contextRead
      ruleAt bindingAt selected structuralSelected bindingSelected variableAdmitted
    have leftSecondRead := assigned_read signature abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq binders injective above second leftMeaning left names depth leftRead leftFixed constantsAbsent secondFresh secondDictionary
    have rightSecondRead := assigned_read signature abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq binders injective above second rightMeaning right names depth rightRead rightFixed constantsAbsent secondFresh secondDictionary
    simpa only [HOLKernelTermCongruence.congruence, HOL.subst] using
      HOLKernelCongruenceReadback.equality_admitted signature abbreviation profile distinct dictionary parameters
        rules binding names antecedent (encodeType signature.symbol base operand) _ _ _ _ antecedentSorted
        (encodeType_sorted signature context base baseSorted operand) leftFirstSorted rightFirstSorted leftSecondSorted rightSecondSorted
        firstProof secondProof g (HOL.subst leftMeaning first) (HOL.subst rightMeaning first)
        (HOL.subst leftMeaning second) (HOL.subst rightMeaning second) (typeRead operand) contextRead
        leftFirstRead rightFirstRead leftSecondRead rightSecondRead ruleAt bindingAt selected treeFirst treeSecond
  | @lam domain gamma result body ih | @all domain gamma body ih | @ex domain gamma body ih =>
    intro left right depth antecedent antecedentSorted leftSorted rightSorted slots independent variableEquality constantTyping
      delta leftMeaning rightMeaning names nodup namesAbove leftRead rightRead leftFixed rightFixed constantsAbsent
      fresh dictionaryFresh g contextRead ruleAt bindingAt selected structuralSelected bindingSelected variableAdmitted
    have head : context[binders depth]? = some (.bound signature.ids.object) := by
      simpa only [Nat.add_zero] using slots 0 (Nat.zero_lt_succ _)
    have bodySlots : ∀ offset < body.binderDepth,
        context[binders (depth + 1 + offset)]? = some (.bound signature.ids.object) := by
      intro offset smaller
      have found := slots (offset + 1) (Nat.add_lt_add_right smaller 1)
      simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using found
    have domainSorted := encodeType_sorted signature context base baseSorted domain
    have boundSorted : Preterm.HasType terms context (.var (binders depth)) [] signature.ids.object :=
      .var (binder := .bound signature.ids.object) head
    let extra := hasType signature.symbol (.var (binders depth)) (encodeType signature.symbol base domain)
    have extraSorted := hasType_sorted signature context boundSorted domainSorted
    let extended := conjunction signature.symbol antecedent extra
    have extendedSorted := conjunction_sorted signature context antecedentSorted extraSorted
    have extendedIndependent : ∀ offset < body.binderDepth,
        ¬ Preterm.HasVar context (binders (depth + 1 + offset)) extended := by
      intro offset smaller
      apply contextExtension_independent context _ _ signature.ids.object signature.symbol _ _ head
      · intro same
        have impossible := injective same
        omega
      · simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using independent (offset + 1) (Nat.add_lt_add_right smaller 1)
      · exact encodeType_independent context _ signature.symbol base (baseIndependent _) domain
    let extendedEqualities : ∀ {type} (index : Var (domain :: gamma) type),
        CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
          (context := context) (hypotheses := [])
          (entails signature.symbol extended (holds signature.symbol
            (equality signature.symbol (encodeType signature.symbol base type)
              (Assignment.extend (.var (binders depth)) left index)
              (Assignment.extend (.var (binders depth)) right index)))) := by
      intro type index
      cases index with
      | vz =>
          exact HOLKernelInferenceProofs.Native.reflexivity signature rules extended _ _ extendedSorted
            domainSorted boundSorted
            (HOLKernelStructuralRules.right signature structural _ _ antecedentSorted extraSorted)
      | vs index =>
          apply HOLKernelStructuralRules.weaken signature structural antecedent extra _
            antecedentSorted extraSorted _ (variableEquality index)
          exact holds_sorted signature context (signature.application context .eqc _
            (.cons (.regular (encodeType_sorted signature context base baseSorted type))
              (.cons (.regular (leftSorted index)) (.cons (.regular (rightSorted index)) .nil))))
    let extendedConstants : ∀ {type} (symbol : Const type),
        CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
          (context := context) (hypotheses := [])
          (typed signature.symbol extended (constant symbol) (encodeType signature.symbol base type)) :=
      HOLKernelTermTyping.weakenConstants signature structural base constant antecedent extra
        antecedentSorted extraSorted baseSorted constantSorted constantTyping
    have extendedLeftSorted : ∀ {type} (index : Var (domain :: gamma) type),
        Preterm.HasType terms context (Assignment.extend (.var (binders depth)) left index)
          [] signature.ids.object :=
      Assignment.extend_sorted signature context (.var (binders depth)) left boundSorted leftSorted
    have extendedRightSorted : ∀ {type} (index : Var (domain :: gamma) type),
        Preterm.HasType terms context (Assignment.extend (.var (binders depth)) right index)
          [] signature.ids.object :=
      Assignment.extend_sorted signature context (.var (binders depth)) right boundSorted rightSorted
    let bodyType : Ty Unit := (fun {type} (_ : Term Const (domain :: gamma) type) => type) body
    let nextNames : Names (domain :: delta) := BinderNames.cons (binders depth) names
    have headFresh : names.lookup? (binders depth) = none := by simpa only [Nat.add_zero] using fresh 0 (Nat.zero_lt_succ _)
    have headDictionary : dictionary (binders depth) = none := by simpa only [Nat.add_zero] using dictionaryFresh 0 (Nat.zero_lt_succ _)
    have nextLookup : LookupPreserving dictionary (Rename.weaken (σ := domain)) names nextNames :=
      LookupPreserving.weaken dictionary names domain (binders depth) headFresh headDictionary
    have nextNodup : nextNames.toList.Nodup :=
      List.nodup_cons.mpr ⟨BinderNames.not_mem_of_lookup?_eq_none names (binders depth) headFresh, nodup⟩
    have nextAbove : ∀ name ∈ nextNames.toList, parameters ≤ name := by
      intro name member
      rcases List.mem_cons.mp member with rfl | member
      · exact above depth
      · exact namesAbove _ member
    have nextConstants : ∀ {type} (symbol : Const type), nextNames.lookup? (indices symbol) = none := by
      intro type symbol
      have apart : binders depth ≠ indices symbol := by have lo := above depth; have hi := bounded symbol; omega
      simp [nextNames, BinderNames.lookup?_cons_of_ne apart, constantsAbsent]
    have nextFresh : ∀ offset < body.binderDepth, nextNames.lookup? (binders (depth + 1 + offset)) = none := by
      intro offset less
      have apart : binders depth ≠ binders (depth + 1 + offset) := by intro same; have wrong := injective same; omega
      have absent : names.lookup? (binders (depth + 1 + offset)) = none := by
        simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using fresh (offset + 1) (Nat.add_lt_add_right less 1)
      simp [nextNames, BinderNames.lookup?_cons_of_ne apart, absent]
    have nextDictionary : ∀ offset < body.binderDepth, dictionary (binders (depth + 1 + offset)) = none := by
      intro offset less
      simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using dictionaryFresh (offset + 1) (Nat.add_lt_add_right less 1)
    have leftNextRead : ∀ {type} (index : Var (domain :: gamma) type),
        HOLKernelLogicalFunctionReadback.reader profile dictionary parameters nextNames
          (Assignment.extend (.var (binders depth)) left index) = some ⟨type, Subst.lift leftMeaning index⟩ := by
      intro type index
      cases index with
      | vz => simp [HOLKernelLogicalFunctionReadback.reader, readTermWith, readVariable, Assignment.extend, Subst.lift, nextNames]
      | vs index =>
          exact logical_reader_weaken_of_read profile dictionary parameters names (left index) domain (binders depth)
            headFresh headDictionary (leftMeaning index) (leftRead index)
    have leftNextFixed : ∀ {type} (index : Var (domain :: gamma) type),
        expandEquivalence signature.symbol abbreviation.reference (Assignment.extend (.var (binders depth)) left index) =
          Assignment.extend (.var (binders depth)) left index := by
      intro type index
      cases index with
      | vz => simp [Assignment.extend, expandEquivalence]
      | vs index => exact leftFixed index
    have rightNextRead : ∀ {type} (index : Var (domain :: gamma) type),
        HOLKernelLogicalFunctionReadback.reader profile dictionary parameters nextNames
          (Assignment.extend (.var (binders depth)) right index) = some ⟨type, Subst.lift rightMeaning index⟩ := by
      intro type index
      cases index with
      | vz => simp [HOLKernelLogicalFunctionReadback.reader, readTermWith, readVariable, Assignment.extend, Subst.lift, nextNames]
      | vs index =>
          exact logical_reader_weaken_of_read profile dictionary parameters names (right index) domain (binders depth)
            headFresh headDictionary (rightMeaning index) (rightRead index)
    have rightNextFixed : ∀ {type} (index : Var (domain :: gamma) type),
        expandEquivalence signature.symbol abbreviation.reference (Assignment.extend (.var (binders depth)) right index) =
          Assignment.extend (.var (binders depth)) right index := by
      intro type index
      cases index with
      | vz => simp [Assignment.extend, expandEquivalence]
      | vs index => exact rightFixed index
    have originalRead := logical_judgment_rename_of_read profile dictionary parameters names nextNames Rename.weaken nextLookup
      (expandEquivalence signature.symbol abbreviation.reference antecedent) g contextRead
    have headRead : HOLKernelLogicalFunctionReadback.reader profile dictionary parameters nextNames (.var (binders depth)) =
        some ⟨domain, Term.var .vz⟩ := by
      simp [HOLKernelLogicalFunctionReadback.reader, readTermWith, readVariable, nextNames]
    have extraRead : readJudgmentWith (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) signature.symbol nextNames
        (expandEquivalence signature.symbol abbreviation.reference extra) = some (.typing (Term.var .vz : Term Const (domain :: delta) domain)) := by
      simp [extra, hasType, applySymbol, Preterm.applyArgs, expandEquivalence, distinct, readJudgmentWith,
        readHead_reference signature.symbol signature.symbol_injective, readTypingWith, typeRead domain, headRead, expect_same]
    let nextG : Judgment Const (domain :: delta) := .conjunction (g.rename Rename.weaken) (.typing (.var .vz))
    have nextContextRead : readJudgmentWith (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) signature.symbol nextNames
        (expandEquivalence signature.symbol abbreviation.reference extended) = some nextG := by
      simp [extended, conjunction, applySymbol, Preterm.applyArgs, expandEquivalence, distinct, readJudgmentWith,
        readHead_reference signature.symbol signature.symbol_injective, originalRead, extraRead, nextG]
    have extendedAdmission : ∀ {type} (index : Var (domain :: gamma) type),
        AdmissionUnderRenaming (context := context) abbreviation profile dictionary parameters ruleAt bindingAt nextNames
          (extendedEqualities index).val (.imp nextG.formula (.eq (Subst.lift leftMeaning index) (Subst.lift rightMeaning index))) := by
      intro type index
      cases index with
      | vz =>
          intro target rho future futureNodup futureAbove related
          have gFuture := logical_judgment_rename_of_read profile dictionary parameters nextNames future rho related
            (expandEquivalence signature.symbol abbreviation.reference extended) nextG nextContextRead
          have headFuture := logical_reader_rename_of_read profile dictionary parameters nextNames future rho related _
            (Term.var .vz : Term Const (domain :: delta) domain) headRead
          have witnessEq : (extendedEqualities (Var.vz : Var (domain :: gamma) domain)).val =
              (HOLKernelInferenceProofs.Native.reflexivity (definitions := definitions) (hypotheses := []) signature rules extended _ _ extendedSorted
                domainSorted boundSorted (HOLKernelStructuralRules.right signature structural antecedent extra antecedentSorted extraSorted)).val := by
            rfl
          refine ⟨2, ?_⟩
          rw [witnessEq]
          simpa only [Assignment.extend, Subst.lift, HOL.rename, Judgment.rename_formula, expandEquivalence] using
            HOLKernelCongruenceReadback.reflexivity_admitted signature abbreviation profile distinct dictionary parameters
              rules future extended (encodeType signature.symbol base domain) (.var (binders depth)) extendedSorted
              domainSorted boundSorted (HOLKernelStructuralRules.right signature structural antecedent extra antecedentSorted extraSorted)
              (nextG.rename rho) (Term.var (rho .vz)) gFuture (typeRead domain)
              (by simpa only [expandEquivalence, HOL.rename] using headFuture) ruleAt bindingAt (selected .reflexivity)
      | vs index =>
          intro target rho future futureNodup futureAbove related
          let composed : Rename Unit delta target := fun index => rho (Var.vs index)
          have together : LookupPreserving dictionary composed names future := nextLookup.comp related
          obtain ⟨fuel, ⟨tree⟩⟩ := variableAdmitted index composed future futureNodup futureAbove together
          have oldContextRead := logical_judgment_rename_of_read profile dictionary parameters names future composed together
            (expandEquivalence signature.symbol abbreviation.reference antecedent) g contextRead
          have futureExtra := logical_judgment_rename_of_read profile dictionary parameters nextNames future rho related
            (expandEquivalence signature.symbol abbreviation.reference extra) (.typing (.var .vz)) extraRead
          have futureLeft := logical_reader_rename_of_read profile dictionary parameters names future composed together _
            (leftMeaning index) (leftRead index)
          have futureRight := logical_reader_rename_of_read profile dictionary parameters names future composed together _
            (rightMeaning index) (rightRead index)
          have equationRead := HOLKernelCongruenceReadback.equation_read signature abbreviation profile distinct dictionary parameters
            future (encodeType signature.symbol base type) (left index) (right index)
            (HOL.rename composed (leftMeaning index)) (HOL.rename composed (rightMeaning index)) (typeRead type)
            (by simpa only [leftFixed] using futureLeft) (by simpa only [rightFixed] using futureRight)
          obtain ⟨weakened⟩ := HOLKernelStructuralReadback.weaken_admitted signature abbreviation (distinct .im) (distinct .an)
            structural (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) parameters future ruleAt bindingAt structuralSelected
            antecedent extra _ antecedentSorted extraSorted
            (holds_sorted signature context (signature.application context .eqc _
              (.cons (.regular (encodeType_sorted signature context base baseSorted type))
                (.cons (.regular (leftSorted index)) (.cons (.regular (rightSorted index)) .nil)))))
            (variableEquality index) (HOL.rename composed g.formula) .top
            (.eq (HOL.rename composed (leftMeaning index)) (HOL.rename composed (rightMeaning index)))
            (by simp only [readFormulaIn, oldContextRead, Option.map_some, Judgment.rename_formula])
            (by simp only [readFormulaIn, futureExtra, Option.map_some, Judgment.rename, Judgment.formula])
            equationRead tree
          have witnessEq : (extendedEqualities (Var.vs index)).val =
              (HOLKernelStructuralRules.weaken signature structural antecedent extra _ antecedentSorted extraSorted
                (holds_sorted signature context (signature.application context .eqc _
                  (.cons (.regular (encodeType_sorted signature context base baseSorted type))
                    (.cons (.regular (leftSorted index)) (.cons (.regular (rightSorted index)) .nil)))))
                (variableEquality index)).val := by
            rfl
          refine ⟨max 1 fuel + 1, ?_⟩
          rw [witnessEq]
          simpa only [Assignment.extend, Subst.lift, HOL.rename, nextG, Judgment.formula,
            Judgment.rename_formula, HOL.weaken, rename_comp, Rename.weaken, composed] using (⟨weakened⟩ : Nonempty _)
    let bodyProof := HOLKernelTermCongruence.congruence signature profile structural typing rules binding base constant binders
      baseSorted constantSorted injective baseIndependent body
      (Assignment.extend (.var (binders depth)) left) (Assignment.extend (.var (binders depth)) right)
      (depth + 1) extended extendedSorted extendedLeftSorted extendedRightSorted bodySlots
      extendedIndependent extendedEqualities extendedConstants
    obtain ⟨bodyFuel, ⟨bodyTree⟩⟩ := ih _ _ (depth + 1) extended extendedSorted extendedLeftSorted extendedRightSorted bodySlots
      extendedIndependent extendedEqualities extendedConstants (Subst.lift leftMeaning) (Subst.lift rightMeaning) nextNames
      nextNodup nextAbove leftNextRead rightNextRead leftNextFixed rightNextFixed nextConstants nextFresh nextDictionary
      nextG nextContextRead ruleAt bindingAt selected structuralSelected bindingSelected extendedAdmission
    have leftBodySorted := encode_sorted signature context base constant binders baseSorted constantSorted
      body _ (depth + 1) extendedLeftSorted bodySlots
    have rightBodySorted := encode_sorted signature context base constant binders baseSorted constantSorted
      body _ (depth + 1) extendedRightSorted bodySlots
    let abstractionEquality := HOLKernelBindingProofs.Native.abstractionCongruence signature binding
      antecedent (encodeType signature.symbol base domain) _ (binders depth) _ _ antecedentSorted domainSorted
      (encodeType_sorted signature context base baseSorted _) head leftBodySorted rightBodySorted
      (by simpa only [Nat.add_zero] using independent 0 (Nat.zero_lt_succ _))
      (HOLKernelTypeSupport.encodeType_independent context _ signature.symbol base (baseIndependent _) domain)
      (HOLKernelTypeSupport.encodeType_independent context _ signature.symbol base (baseIndependent _) _) bodyProof
    have leftLambdaRead := assigned_read signature abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq binders injective above (Term.lam body) leftMeaning left names depth leftRead leftFixed constantsAbsent fresh dictionaryFresh
    have rightLambdaRead := assigned_read signature abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq binders injective above (Term.lam body) rightMeaning right names depth rightRead rightFixed constantsAbsent fresh dictionaryFresh
    have lambdaEquationRead := HOLKernelCongruenceReadback.equation_read signature abbreviation profile distinct dictionary parameters
      names (encodeType signature.symbol base (domain ⇒ bodyType)) _ _
      (Term.lam (HOL.subst (Subst.lift leftMeaning) body)) (Term.lam (HOL.subst (Subst.lift rightMeaning) body))
      (typeRead _) leftLambdaRead rightLambdaRead
    have lambdaConclusionRead : readFormulaIn abbreviation (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters)
        parameters names (entails signature.symbol antecedent (holds signature.symbol
          (equality signature.symbol (encodeType signature.symbol base (domain ⇒ bodyType))
            (encodeWithAssignment signature.symbol base constant binders left depth (Term.lam body))
            (encodeWithAssignment signature.symbol base constant binders right depth (Term.lam body))))) =
        some (.imp g.formula (.eq (.lam (HOL.subst (Subst.lift leftMeaning) body)) (.lam (HOL.subst (Subst.lift rightMeaning) body)))) := by
      rw [HOLKernelStructuralReadback.read_entails abbreviation signature.symbol_injective (distinct .im), lambdaEquationRead]
      simp only [readFormulaIn, contextRead, Option.map_some]
      rfl
    have rootFresh : HOLKernelBindingInterpretation.freshName parameters names (binders depth) = true := by
      simp [HOLKernelBindingInterpretation.freshName, headFresh, above]
    let lambdaTree : AdmittedProof abbreviation theorems context (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters)
        parameters ruleAt bindingAt (bodyFuel + 1) names abstractionEquality.val
        (.imp g.formula (.eq (.lam (HOL.subst (Subst.lift leftMeaning) body)) (.lam (HOL.subst (Subst.lift rightMeaning) body)))) :=
      AdmittedStep.binding abstractionEquality.property.eval {
        rule := .abstractionCongruence
        selected := bindingSelected
        declared := binding.declared .abstractionCongruence
        conclusion_read := lambdaConclusionRead
        step := .abstractionCongruence rootFresh (by
          simpa only [nextG, Judgment.formula, Judgment.rename_formula, HOL.weaken] using bodyTree) }
    first
    | refine ⟨bodyFuel + 1, ?_⟩
      simpa only [HOLKernelTermCongruence.congruence, HOL.subst] using (⟨lambdaTree⟩ : Nonempty _)
    | have leftBodyRead := assigned_read signature abbreviation profile distinct dictionary indices parameters lookup bounded
        base constant baseEq constantEq binders injective above body (Subst.lift leftMeaning) _ nextNames (depth + 1)
        leftNextRead leftNextFixed nextConstants nextFresh nextDictionary
      have rightBodyRead := assigned_read signature abbreviation profile distinct dictionary indices parameters lookup bounded
        base constant baseEq constantEq binders injective above body (Subst.lift rightMeaning) _ nextNames (depth + 1)
        rightNextRead rightNextFixed nextConstants nextFresh nextDictionary
      first
      | refine ⟨max 1 (bodyFuel + 1) + 2, ?_⟩
        simpa only [HOLKernelTermCongruence.congruence, HOL.subst] using
          HOLKernelCongruenceReadback.universal_admitted signature abbreviation profile distinct dictionary parameters
            rules names antecedent (encodeType signature.symbol base domain) _ _ (binders depth) (binders depth)
            antecedentSorted domainSorted head head leftBodySorted rightBodySorted abstractionEquality g
            (HOL.subst (Subst.lift leftMeaning) body) (HOL.subst (Subst.lift rightMeaning) body) contextRead (typeRead domain)
            (above depth) (above depth) leftBodyRead rightBodyRead ruleAt bindingAt (selected .applicationArgument) lambdaTree
      | refine ⟨max 1 (bodyFuel + 1) + 2, ?_⟩
        simpa only [HOLKernelTermCongruence.congruence, HOL.subst] using
          HOLKernelCongruenceReadback.existential_admitted signature abbreviation profile distinct dictionary parameters
            rules names antecedent (encodeType signature.symbol base domain) _ _ (binders depth) (binders depth)
            antecedentSorted domainSorted head head leftBodySorted rightBodySorted abstractionEquality g
            (HOL.subst (Subst.lift leftMeaning) body) (HOL.subst (Subst.lift rightMeaning) body) contextRead (typeRead domain)
            (above depth) (above depth) leftBodyRead rightBodyRead ruleAt bindingAt (selected .applicationArgument) lambdaTree


#print axioms assigned_read
#print axioms congruence_admitted
end Mettapedia.Languages.MM0.HOLKernelTermCongruenceReadback
