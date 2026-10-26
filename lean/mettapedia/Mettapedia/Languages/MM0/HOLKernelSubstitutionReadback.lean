import Mettapedia.Languages.MM0.HOLKernelTermCongruenceReadback
import Mettapedia.Languages.MM0.HOLKernelAlphaReadback
import Mettapedia.Languages.MM0.HOLKernelSubstitution

/-!
# Admission of native source-substitution comparison receipts

The actual recursive comparison between literal native substitution and
encoding intrinsic HOL substitution produces independently admitted proof
receipts through all thirteen source term constructors. Both endpoint readings
are the same renamed intrinsic substitution, while their raw native encodings
may differ.

The shared binding case rebinds each compound image, weakens those receipts,
applies pointwise assignment congruence, and joins the recursive lifted
substitution comparison. The native witness survives the assignment-lift cast.
Fresh name banks, occurrence independence, constant lookup, the retained
antecedent and the actual theorem-selection policy remain explicit. Native
beta and quantifier-instantiation constructions consume the single-variable
instance comparison proved here. Its retained argument-equality assumption
relates the body reading to the instantiated result.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.MM0.HOLKernelSubstitutionReadback
open Mettapedia.Logic Mettapedia.Logic.HOL
open Kernel HOLKernelSyntax HOLKernelJudgment HOLKernelTermAssignments HOLKernelTypeSupport
open HOLKernelTermReadback HOLKernelJudgmentReadback HOLKernelRuleReadback HOLKernelProofReadback
open HOLKernelTypingRules (typed boolType functionType)
open HOLKernelInferenceRules (equality)
open HOLKernelStructuralRules (CheckedProof)
open NamedElaboration (BinderNames)
universe u
variable {Const : Ty Unit → Type u}
variable {sorts : SortSignature} {terms : TermSignature} {definitions : Definition.Signature}
variable {theorems : TheoremSignature} {context : Context}

private theorem encoded_fixed (signature : Signature sorts terms)
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (distinct : ∀ symbol, signature.symbol symbol ≠ abbreviation.reference)
    (base : Unit → Preterm) (constant : ∀ {type}, Const type → Preterm)
    (baseEq : base = fun _ => .var 0) (indices : ∀ {type}, Const type → Nat)
    (constantEq : ∀ {type} (symbol : Const type), constant symbol = .var (indices symbol))
    (binders : Nat → Nat) {gamma delta : Ctx Unit} (rho : Rename Unit gamma delta)
    (names : Names delta) (assignment : Assignment gamma)
    (assignmentEq : ∀ {type} (index : Var gamma type), assignment index = .var (names.nameOf (rho index)))
    {type : Ty Unit} (source : Term Const gamma type) (depth : Nat) :
    expandEquivalence signature.symbol abbreviation.reference
      (encodeWithAssignment signature.symbol base constant binders assignment depth source) =
        encodeWithAssignment signature.symbol base constant binders assignment depth source := by
  exact expandEquivalence_encodeWithAssignment_of_fixed signature.symbol abbreviation.reference distinct base constant binders
    (fun _ => by simp [baseEq, expandEquivalence]) (fun symbol => by simp [constantEq, expandEquivalence])
    source assignment depth (fun index => by simp [assignmentEq, expandEquivalence])

#print axioms encoded_fixed

theorem substitution_read (signature : Signature sorts terms)
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
    {gamma delta target : Ctx Unit} {type : Ty Unit} (source : Term Const gamma type)
    (substitution : Subst Const gamma delta) (assignment : Assignment delta) (depth : Nat)
    (rho : Rename Unit delta target) (names : Names target)
    (nodup : names.toList.Nodup) (namesAbove : ∀ name ∈ names.toList, parameters ≤ name)
    (assignmentEq : ∀ {type} (index : Var delta type), assignment index = .var (names.nameOf (rho index)))
    (fresh : ∀ offset < source.binderDepth + Subst.maxBinderDepth substitution, binders (depth + offset) ∉ names.toList)
    (dictionaryFresh : ∀ offset < source.binderDepth + Subst.maxBinderDepth substitution, dictionary (binders (depth + offset)) = none) :
    HOLKernelLogicalFunctionReadback.reader profile dictionary parameters names
      (expandEquivalence signature.symbol abbreviation.reference
        (encodeWithAssignment signature.symbol base constant binders
          (encodeSubstitution signature.symbol base constant binders assignment depth substitution) depth source)) =
      some ⟨type, HOL.rename rho (HOL.subst substitution source)⟩ ∧
    HOLKernelLogicalFunctionReadback.reader profile dictionary parameters names
      (expandEquivalence signature.symbol abbreviation.reference
        (encodeWithAssignment signature.symbol base constant binders assignment depth (HOL.subst substitution source))) =
      some ⟨type, HOL.rename rho (HOL.subst substitution source)⟩ := by
  have constantsAbsent : ∀ {type} (symbol : Const type), names.lookup? (indices symbol) = none := by
    intro type symbol
    apply BinderNames.lookup?_none_of_not_mem
    intro member
    have lo := namesAbove _ member
    have hi := bounded symbol
    omega
  have imagesFixed : ∀ {type} (index : Var gamma type),
      expandEquivalence signature.symbol abbreviation.reference
        (encodeSubstitution signature.symbol base constant binders assignment depth substitution index) =
      encodeSubstitution signature.symbol base constant binders assignment depth substitution index := by
    intro type index
    exact encoded_fixed signature abbreviation distinct base constant baseEq indices constantEq binders rho names assignment assignmentEq (substitution index) depth
  have imageReads : ∀ {type} (index : Var gamma type),
      HOLKernelLogicalFunctionReadback.reader profile dictionary parameters names
        (encodeSubstitution signature.symbol base constant binders assignment depth substitution index) =
      some ⟨type, HOL.rename rho (substitution index)⟩ := by
    intro type index
    have image := HOLKernelAlphaReadback.encoded_read abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq rho names assignment assignmentEq binders injective above (substitution index) depth nodup namesAbove
      (by
        intro offset less type sourceIndex
        exact BinderNames.ne_nameOf_of_not_mem names
          (fresh offset (Nat.lt_of_lt_of_le less (Nat.le_trans (Subst.binderDepth_le_maxBinderDepth substitution index) (Nat.le_add_left _ _))))
          (rho sourceIndex))
    change HOLKernelLogicalFunctionReadback.reader profile dictionary parameters names
      (expandEquivalence signature.symbol abbreviation.reference
        (encodeSubstitution signature.symbol base constant binders assignment depth substitution index)) = _ at image
    rw [imagesFixed] at image
    exact image
  constructor
  · have reading := HOLKernelTermCongruenceReadback.assigned_read signature abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq binders injective above source (fun index => HOL.rename rho (substitution index))
      (encodeSubstitution signature.symbol base constant binders assignment depth substitution) names depth imageReads imagesFixed constantsAbsent
      (fun offset less => BinderNames.lookup?_none_of_not_mem names (fresh offset (Nat.lt_of_lt_of_le less (Nat.le_add_right _ _))))
      (fun offset less => dictionaryFresh offset (Nat.lt_of_lt_of_le less (Nat.le_add_right _ _)))
    have composition : HOL.rename rho (HOL.subst substitution source) =
        HOL.subst (fun index => HOL.rename rho (substitution index)) source := rename_subst rho substitution source
    rw [composition]
    exact reading
  · exact HOLKernelAlphaReadback.encoded_read abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq rho names assignment assignmentEq binders injective above (HOL.subst substitution source) depth nodup namesAbove
      (by
        intro offset less type index
        exact BinderNames.ne_nameOf_of_not_mem names
          (fresh offset (Nat.lt_of_lt_of_le less (Term.binderDepth_subst_le source substitution))) (rho index))

#print axioms substitution_read

theorem compile_admitted (signature : Signature sorts terms)
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
    (binders temporary : Nat → Nat)
    (baseSorted : ∀ index, Preterm.HasType terms context (base index) [] signature.ids.type)
    (constantSorted : ∀ {type} (symbol : Const type), Preterm.HasType terms context (constant symbol) [] signature.ids.object)
    (bindersInjective : Function.Injective binders) (temporaryInjective : Function.Injective temporary)
    (bindersAbove : ∀ level, parameters ≤ binders level) (temporaryAbove : ∀ level, parameters ≤ temporary level)
    (baseIndependent : ∀ slot index, ¬ Preterm.HasVar context (binders slot) (base index))
    (temporaryIndependent : ∀ slot index, ¬ Preterm.HasVar context (temporary slot) (base index))
    {gamma : Ctx Unit} {type : Ty Unit} (source : Term Const gamma type) :
    ∀ {delta : Ctx Unit} (substitution : Subst Const gamma delta) (assignment : Assignment delta)
      (depth temporaryDepth : Nat) (antecedent : Preterm)
      (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
      (assignmentSorted : ∀ {type} (index : Var delta type), Preterm.HasType terms context (assignment index) [] signature.ids.object)
      (slots : ∀ offset < source.binderDepth + Subst.maxBinderDepth substitution,
        context[binders (depth + offset)]? = some (.bound signature.ids.object))
      (temporarySlots : ∀ offset < source.binderDepth + Subst.maxBinderDepth substitution,
        context[temporary (temporaryDepth + offset)]? = some (.bound signature.ids.object))
      (fresh : ∀ offset < source.binderDepth + Subst.maxBinderDepth substitution, ¬ Preterm.HasVar context (binders (depth + offset)) antecedent)
      (temporaryFresh : ∀ offset < source.binderDepth + Subst.maxBinderDepth substitution, ¬ Preterm.HasVar context (temporary (temporaryDepth + offset)) antecedent)
      (disjoint : ∀ first < source.binderDepth + Subst.maxBinderDepth substitution, ∀ second < source.binderDepth + Subst.maxBinderDepth substitution,
        binders (depth + first) ≠ temporary (temporaryDepth + second))
      (variableTyping : ∀ {type} (index : Var delta type),
        CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems) (context := context) (hypotheses := [])
          (typed signature.symbol antecedent (assignment index) (encodeType signature.symbol base type)))
      (constantTyping : ∀ {type} (symbol : Const type),
        CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems) (context := context) (hypotheses := [])
          (typed signature.symbol antecedent (constant symbol) (encodeType signature.symbol base type)))
      {target : Ctx Unit} (rho : Rename Unit delta target) (names : Names target)
      (_ : names.toList.Nodup) (_ : ∀ name ∈ names.toList, parameters ≤ name)
      (_ : ∀ {type} (index : Var delta type), assignment index = .var (names.nameOf (rho index)))
      (_ : ∀ offset < source.binderDepth + Subst.maxBinderDepth substitution, binders (depth + offset) ∉ names.toList)
      (_ : ∀ offset < source.binderDepth + Subst.maxBinderDepth substitution, temporary (temporaryDepth + offset) ∉ names.toList)
      (_ : ∀ offset < source.binderDepth + Subst.maxBinderDepth substitution, dictionary (binders (depth + offset)) = none)
      (g : Judgment Const target)
      (_ : readJudgmentWith (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) signature.symbol names
        (expandEquivalence signature.symbol abbreviation.reference antecedent) = some g)
      (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
      (_ : ∀ rule, ruleAt (rules.index rule) = some (.inference rule))
      (_ : ∀ rule, ruleAt (structural.index rule) = some (.structural rule))
      (_ : ∀ rule, bindingAt (binding.index rule) = some rule),
      ∃ fuel, Nonempty (AdmittedProof abbreviation theorems context
        (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) parameters ruleAt bindingAt fuel names
        (HOLKernelSubstitution.compile signature profile structural typing rules binding base constant binders temporary
          baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent source substitution assignment
          depth temporaryDepth antecedent antecedentSorted assignmentSorted slots temporarySlots fresh temporaryFresh disjoint
          variableTyping constantTyping).val
        (.imp g.formula (.eq (HOL.rename rho (HOL.subst substitution source)) (HOL.rename rho (HOL.subst substitution source))))) := by
  have typeRead (type : Ty Unit) : readType signature.symbol
      (expandEquivalence signature.symbol abbreviation.reference (encodeType signature.symbol base type)) = some type := by
    rw [baseEq, expandEquivalence_encodeType_of_fixed signature.symbol abbreviation.reference distinct
      (fun _ : Unit => .var 0) (fun _ => by simp [expandEquivalence])]
    exact readType_encode signature.symbol signature.symbol_injective type
  induction source with
  | var index =>
    intro delta substitution assignment depth temporaryDepth antecedent antecedentSorted assignmentSorted slots temporarySlots
      fresh temporaryFresh disjoint variableTyping constantTyping target rho names nodup namesAbove assignmentEq sourceNames temporaryNames
      dictionaryFresh g contextRead ruleAt bindingAt selected structuralSelected bindingSelected
    have reading := HOLKernelAlphaReadback.encoded_read abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq rho names assignment assignmentEq binders bindersInjective bindersAbove
      (substitution index) depth nodup namesAbove
      (by
        intro offset less type sourceIndex
        exact BinderNames.ne_nameOf_of_not_mem names (sourceNames offset
          (by have h := Subst.binderDepth_le_maxBinderDepth substitution index; simp only [Term.binderDepth, Nat.zero_add]; omega)) (rho sourceIndex))
    refine ⟨2, ?_⟩
    simpa only [HOLKernelSubstitution.compile, encodeWithAssignment, encodeSubstitution, HOL.subst] using
      HOLKernelCongruenceReadback.reflexivity_admitted signature abbreviation profile distinct dictionary parameters
        rules names antecedent (encodeType signature.symbol base _) _ antecedentSorted
        (encodeType_sorted signature context base baseSorted _)
        ((encodeSubstitution_sorted signature context base constant binders baseSorted constantSorted substitution assignment depth assignmentSorted
          (fun offset smaller => slots offset (by simpa only [Term.binderDepth, Nat.zero_add] using smaller))) index)
        ((HOLKernelTermTyping.substitutionTyping signature structural typing base constant binders baseSorted constantSorted bindersInjective baseIndependent
          substitution assignment depth antecedent antecedentSorted assignmentSorted
          (fun offset smaller => slots offset (by simpa only [Term.binderDepth, Nat.zero_add] using smaller))
          (fun offset smaller => fresh offset (by simpa only [Term.binderDepth, Nat.zero_add] using smaller)) variableTyping constantTyping) index)
        g (HOL.rename rho (substitution index)) contextRead (typeRead _) reading ruleAt bindingAt (selected .reflexivity)
  | const symbol =>
    intro delta substitution assignment depth temporaryDepth antecedent antecedentSorted assignmentSorted slots temporarySlots
      fresh temporaryFresh disjoint variableTyping constantTyping target rho names nodup namesAbove assignmentEq sourceNames temporaryNames
      dictionaryFresh g contextRead ruleAt bindingAt selected structuralSelected bindingSelected
    have reading := HOLKernelAlphaReadback.encoded_read abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq rho names assignment assignmentEq binders bindersInjective bindersAbove (Term.const symbol) depth nodup namesAbove
      (by intro offset less; simp only [Term.binderDepth] at less; omega)
    refine ⟨2, ?_⟩
    simpa only [HOLKernelSubstitution.compile, encodeWithAssignment, HOL.subst, HOL.rename, encodeType] using
      HOLKernelCongruenceReadback.reflexivity_admitted signature abbreviation profile distinct dictionary parameters
        rules names antecedent (encodeType signature.symbol base _) (constant symbol) antecedentSorted
        (encodeType_sorted signature context base baseSorted _) (constantSorted symbol) (constantTyping symbol)
        g (Term.const symbol) contextRead (typeRead _) reading ruleAt bindingAt (selected .reflexivity)
  | top =>
    intro delta substitution assignment depth temporaryDepth antecedent antecedentSorted assignmentSorted slots temporarySlots
      fresh temporaryFresh disjoint variableTyping constantTyping target rho names nodup namesAbove assignmentEq sourceNames temporaryNames
      dictionaryFresh g contextRead ruleAt bindingAt selected structuralSelected bindingSelected
    have reading := HOLKernelAlphaReadback.encoded_read abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq rho names assignment assignmentEq binders bindersInjective bindersAbove (Term.top : Formula Const _) depth nodup namesAbove
      (by intro offset less; simp only [Term.binderDepth] at less; omega)
    refine ⟨2, ?_⟩
    simpa only [HOLKernelSubstitution.compile, encodeWithAssignment, HOL.subst, HOL.rename, encodeType] using
      HOLKernelCongruenceReadback.reflexivity_admitted signature abbreviation profile distinct dictionary parameters
        rules names antecedent (encodeType signature.symbol base .prop) (applySymbol signature.symbol .truth []) antecedentSorted
        (encodeType_sorted signature context base baseSorted .prop) (signature.application context .truth [] .nil) (HOLKernelTypingProofs.truthTyping signature typing antecedent antecedentSorted)
        g (Term.top : Formula Const _) contextRead (typeRead _) reading ruleAt bindingAt (selected .reflexivity)
  | bot =>
    intro delta substitution assignment depth temporaryDepth antecedent antecedentSorted assignmentSorted slots temporarySlots
      fresh temporaryFresh disjoint variableTyping constantTyping target rho names nodup namesAbove assignmentEq sourceNames temporaryNames
      dictionaryFresh g contextRead ruleAt bindingAt selected structuralSelected bindingSelected
    have reading := HOLKernelAlphaReadback.encoded_read abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq rho names assignment assignmentEq binders bindersInjective bindersAbove (Term.bot : Formula Const _) depth nodup namesAbove
      (by intro offset less; simp only [Term.binderDepth] at less; omega)
    refine ⟨2, ?_⟩
    simpa only [HOLKernelSubstitution.compile, encodeWithAssignment, HOL.subst, HOL.rename, encodeType] using
      HOLKernelCongruenceReadback.reflexivity_admitted signature abbreviation profile distinct dictionary parameters
        rules names antecedent (encodeType signature.symbol base .prop) (applySymbol signature.symbol .falsity []) antecedentSorted
        (encodeType_sorted signature context base baseSorted .prop) (signature.application context .falsity [] .nil) (HOLKernelTypingProofs.falsityTyping signature typing antecedent antecedentSorted)
        g (Term.bot : Formula Const _) contextRead (typeRead _) reading ruleAt bindingAt (selected .reflexivity)
  | @app gamma domain result first second ihFirst ihSecond =>
    intro delta substitution assignment depth temporaryDepth antecedent antecedentSorted assignmentSorted slots temporarySlots
      fresh temporaryFresh disjoint variableTyping constantTyping target rho names nodup namesAbove assignmentEq sourceNames temporaryNames
      dictionaryFresh g contextRead ruleAt bindingAt selected structuralSelected bindingSelected
    have firstBudget : first.binderDepth + Subst.maxBinderDepth substitution ≤
        max first.binderDepth second.binderDepth + Subst.maxBinderDepth substitution :=
      Nat.add_le_add_right (Nat.le_max_left _ _) _
    have firstSlots := fun offset smaller => slots offset (Nat.lt_of_lt_of_le smaller firstBudget)
    have firstTemporarySlots := fun offset smaller => temporarySlots offset (Nat.lt_of_lt_of_le smaller firstBudget)
    have firstFresh := fun offset smaller => fresh offset (Nat.lt_of_lt_of_le smaller firstBudget)
    have firstTemporaryFresh := fun offset smaller => temporaryFresh offset (Nat.lt_of_lt_of_le smaller firstBudget)
    have firstDisjoint := fun firstOffset firstSmaller secondOffset secondSmaller =>
      disjoint firstOffset (Nat.lt_of_lt_of_le firstSmaller firstBudget)
        secondOffset (Nat.lt_of_lt_of_le secondSmaller firstBudget)
    have firstSorted := substitution_encodings_sorted signature context base constant binders baseSorted
      constantSorted first substitution assignment depth assignmentSorted firstSlots
    let firstProof := HOLKernelSubstitution.compile signature profile structural typing rules binding base constant binders temporary
      baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent
      first substitution assignment depth temporaryDepth antecedent antecedentSorted assignmentSorted
      firstSlots firstTemporarySlots firstFresh firstTemporaryFresh firstDisjoint variableTyping constantTyping
    have secondBudget : second.binderDepth + Subst.maxBinderDepth substitution ≤
        max first.binderDepth second.binderDepth + Subst.maxBinderDepth substitution :=
      Nat.add_le_add_right (Nat.le_max_right _ _) _
    have secondSlots := fun offset smaller => slots offset (Nat.lt_of_lt_of_le smaller secondBudget)
    have secondTemporarySlots := fun offset smaller => temporarySlots offset (Nat.lt_of_lt_of_le smaller secondBudget)
    have secondFresh := fun offset smaller => fresh offset (Nat.lt_of_lt_of_le smaller secondBudget)
    have secondTemporaryFresh := fun offset smaller => temporaryFresh offset (Nat.lt_of_lt_of_le smaller secondBudget)
    have secondDisjoint := fun firstOffset firstSmaller secondOffset secondSmaller =>
      disjoint firstOffset (Nat.lt_of_lt_of_le firstSmaller secondBudget)
        secondOffset (Nat.lt_of_lt_of_le secondSmaller secondBudget)
    have secondSorted := substitution_encodings_sorted signature context base constant binders baseSorted
      constantSorted second substitution assignment depth assignmentSorted secondSlots
    let secondProof := HOLKernelSubstitution.compile signature profile structural typing rules binding base constant binders temporary
      baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent
      second substitution assignment depth temporaryDepth antecedent antecedentSorted assignmentSorted
      secondSlots secondTemporarySlots secondFresh secondTemporaryFresh secondDisjoint variableTyping constantTyping
    have firstNames := fun offset less => sourceNames offset (Nat.lt_of_lt_of_le less firstBudget)
    have firstTemporaryNames := fun offset less => temporaryNames offset (Nat.lt_of_lt_of_le less firstBudget)
    have firstDictionary := fun offset less => dictionaryFresh offset (Nat.lt_of_lt_of_le less firstBudget)
    obtain ⟨fuelFirst, ⟨treeFirst⟩⟩ := ihFirst substitution assignment depth temporaryDepth antecedent antecedentSorted assignmentSorted
      firstSlots firstTemporarySlots firstFresh firstTemporaryFresh firstDisjoint variableTyping constantTyping
      rho names nodup namesAbove assignmentEq firstNames firstTemporaryNames firstDictionary g contextRead ruleAt bindingAt
      selected structuralSelected bindingSelected
    obtain ⟨leftFirstRead, rightFirstRead⟩ := substitution_read signature abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq binders bindersInjective bindersAbove first substitution assignment depth rho names nodup namesAbove assignmentEq firstNames firstDictionary
    have secondNames := fun offset less => sourceNames offset (Nat.lt_of_lt_of_le less secondBudget)
    have secondTemporaryNames := fun offset less => temporaryNames offset (Nat.lt_of_lt_of_le less secondBudget)
    have secondDictionary := fun offset less => dictionaryFresh offset (Nat.lt_of_lt_of_le less secondBudget)
    obtain ⟨fuelSecond, ⟨treeSecond⟩⟩ := ihSecond substitution assignment depth temporaryDepth antecedent antecedentSorted assignmentSorted
      secondSlots secondTemporarySlots secondFresh secondTemporaryFresh secondDisjoint variableTyping constantTyping
      rho names nodup namesAbove assignmentEq secondNames secondTemporaryNames secondDictionary g contextRead ruleAt bindingAt
      selected structuralSelected bindingSelected
    obtain ⟨leftSecondRead, rightSecondRead⟩ := substitution_read signature abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq binders bindersInjective bindersAbove second substitution assignment depth rho names nodup namesAbove assignmentEq secondNames secondDictionary
    simpa only [HOLKernelSubstitution.compile, HOL.subst, HOL.rename] using
      HOLKernelCongruenceReadback.application_admitted signature abbreviation profile distinct dictionary parameters rules binding names
        antecedent (encodeType signature.symbol base domain) (encodeType signature.symbol base result) _ _ _ _ antecedentSorted
        (encodeType_sorted signature context base baseSorted domain) (encodeType_sorted signature context base baseSorted result)
        firstSorted.1 firstSorted.2 secondSorted.1 secondSorted.2 firstProof secondProof g
        (HOL.rename rho (HOL.subst substitution first)) (HOL.rename rho (HOL.subst substitution first))
        (HOL.rename rho (HOL.subst substitution second)) (HOL.rename rho (HOL.subst substitution second))
        contextRead (typeRead domain) (typeRead result) leftFirstRead rightFirstRead leftSecondRead rightSecondRead ruleAt bindingAt selected treeFirst treeSecond
  | @and gamma first second ihFirst ihSecond =>
    intro delta substitution assignment depth temporaryDepth antecedent antecedentSorted assignmentSorted slots temporarySlots
      fresh temporaryFresh disjoint variableTyping constantTyping target rho names nodup namesAbove assignmentEq sourceNames temporaryNames
      dictionaryFresh g contextRead ruleAt bindingAt selected structuralSelected bindingSelected
    have firstBudget : first.binderDepth + Subst.maxBinderDepth substitution ≤
        max first.binderDepth second.binderDepth + Subst.maxBinderDepth substitution :=
      Nat.add_le_add_right (Nat.le_max_left _ _) _
    have firstSlots := fun offset smaller => slots offset (Nat.lt_of_lt_of_le smaller firstBudget)
    have firstTemporarySlots := fun offset smaller => temporarySlots offset (Nat.lt_of_lt_of_le smaller firstBudget)
    have firstFresh := fun offset smaller => fresh offset (Nat.lt_of_lt_of_le smaller firstBudget)
    have firstTemporaryFresh := fun offset smaller => temporaryFresh offset (Nat.lt_of_lt_of_le smaller firstBudget)
    have firstDisjoint := fun firstOffset firstSmaller secondOffset secondSmaller =>
      disjoint firstOffset (Nat.lt_of_lt_of_le firstSmaller firstBudget)
        secondOffset (Nat.lt_of_lt_of_le secondSmaller firstBudget)
    have firstSorted := substitution_encodings_sorted signature context base constant binders baseSorted
      constantSorted first substitution assignment depth assignmentSorted firstSlots
    let firstProof := HOLKernelSubstitution.compile signature profile structural typing rules binding base constant binders temporary
      baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent
      first substitution assignment depth temporaryDepth antecedent antecedentSorted assignmentSorted
      firstSlots firstTemporarySlots firstFresh firstTemporaryFresh firstDisjoint variableTyping constantTyping
    have secondBudget : second.binderDepth + Subst.maxBinderDepth substitution ≤
        max first.binderDepth second.binderDepth + Subst.maxBinderDepth substitution :=
      Nat.add_le_add_right (Nat.le_max_right _ _) _
    have secondSlots := fun offset smaller => slots offset (Nat.lt_of_lt_of_le smaller secondBudget)
    have secondTemporarySlots := fun offset smaller => temporarySlots offset (Nat.lt_of_lt_of_le smaller secondBudget)
    have secondFresh := fun offset smaller => fresh offset (Nat.lt_of_lt_of_le smaller secondBudget)
    have secondTemporaryFresh := fun offset smaller => temporaryFresh offset (Nat.lt_of_lt_of_le smaller secondBudget)
    have secondDisjoint := fun firstOffset firstSmaller secondOffset secondSmaller =>
      disjoint firstOffset (Nat.lt_of_lt_of_le firstSmaller secondBudget)
        secondOffset (Nat.lt_of_lt_of_le secondSmaller secondBudget)
    have secondSorted := substitution_encodings_sorted signature context base constant binders baseSorted
      constantSorted second substitution assignment depth assignmentSorted secondSlots
    let secondProof := HOLKernelSubstitution.compile signature profile structural typing rules binding base constant binders temporary
      baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent
      second substitution assignment depth temporaryDepth antecedent antecedentSorted assignmentSorted
      secondSlots secondTemporarySlots secondFresh secondTemporaryFresh secondDisjoint variableTyping constantTyping
    have firstNames := fun offset less => sourceNames offset (Nat.lt_of_lt_of_le less firstBudget)
    have firstTemporaryNames := fun offset less => temporaryNames offset (Nat.lt_of_lt_of_le less firstBudget)
    have firstDictionary := fun offset less => dictionaryFresh offset (Nat.lt_of_lt_of_le less firstBudget)
    obtain ⟨fuelFirst, ⟨treeFirst⟩⟩ := ihFirst substitution assignment depth temporaryDepth antecedent antecedentSorted assignmentSorted
      firstSlots firstTemporarySlots firstFresh firstTemporaryFresh firstDisjoint variableTyping constantTyping
      rho names nodup namesAbove assignmentEq firstNames firstTemporaryNames firstDictionary g contextRead ruleAt bindingAt
      selected structuralSelected bindingSelected
    obtain ⟨leftFirstRead, rightFirstRead⟩ := substitution_read signature abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq binders bindersInjective bindersAbove first substitution assignment depth rho names nodup namesAbove assignmentEq firstNames firstDictionary
    have secondNames := fun offset less => sourceNames offset (Nat.lt_of_lt_of_le less secondBudget)
    have secondTemporaryNames := fun offset less => temporaryNames offset (Nat.lt_of_lt_of_le less secondBudget)
    have secondDictionary := fun offset less => dictionaryFresh offset (Nat.lt_of_lt_of_le less secondBudget)
    obtain ⟨fuelSecond, ⟨treeSecond⟩⟩ := ihSecond substitution assignment depth temporaryDepth antecedent antecedentSorted assignmentSorted
      secondSlots secondTemporarySlots secondFresh secondTemporaryFresh secondDisjoint variableTyping constantTyping
      rho names nodup namesAbove assignmentEq secondNames secondTemporaryNames secondDictionary g contextRead ruleAt bindingAt
      selected structuralSelected bindingSelected
    obtain ⟨leftSecondRead, rightSecondRead⟩ := substitution_read signature abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq binders bindersInjective bindersAbove second substitution assignment depth rho names nodup namesAbove assignmentEq secondNames secondDictionary
    simpa only [HOLKernelSubstitution.compile, HOL.subst, HOL.rename] using
      HOLKernelCongruenceReadback.conjunction_admitted signature abbreviation profile distinct dictionary parameters rules binding names
        antecedent _ _ _ _ antecedentSorted firstSorted.1 firstSorted.2 secondSorted.1 secondSorted.2 firstProof secondProof g
        (HOL.rename rho (HOL.subst substitution first)) (HOL.rename rho (HOL.subst substitution first))
        (HOL.rename rho (HOL.subst substitution second)) (HOL.rename rho (HOL.subst substitution second))
        contextRead leftFirstRead rightFirstRead leftSecondRead rightSecondRead ruleAt bindingAt selected treeFirst treeSecond
  | @or gamma first second ihFirst ihSecond =>
    intro delta substitution assignment depth temporaryDepth antecedent antecedentSorted assignmentSorted slots temporarySlots
      fresh temporaryFresh disjoint variableTyping constantTyping target rho names nodup namesAbove assignmentEq sourceNames temporaryNames
      dictionaryFresh g contextRead ruleAt bindingAt selected structuralSelected bindingSelected
    have firstBudget : first.binderDepth + Subst.maxBinderDepth substitution ≤
        max first.binderDepth second.binderDepth + Subst.maxBinderDepth substitution :=
      Nat.add_le_add_right (Nat.le_max_left _ _) _
    have firstSlots := fun offset smaller => slots offset (Nat.lt_of_lt_of_le smaller firstBudget)
    have firstTemporarySlots := fun offset smaller => temporarySlots offset (Nat.lt_of_lt_of_le smaller firstBudget)
    have firstFresh := fun offset smaller => fresh offset (Nat.lt_of_lt_of_le smaller firstBudget)
    have firstTemporaryFresh := fun offset smaller => temporaryFresh offset (Nat.lt_of_lt_of_le smaller firstBudget)
    have firstDisjoint := fun firstOffset firstSmaller secondOffset secondSmaller =>
      disjoint firstOffset (Nat.lt_of_lt_of_le firstSmaller firstBudget)
        secondOffset (Nat.lt_of_lt_of_le secondSmaller firstBudget)
    have firstSorted := substitution_encodings_sorted signature context base constant binders baseSorted
      constantSorted first substitution assignment depth assignmentSorted firstSlots
    let firstProof := HOLKernelSubstitution.compile signature profile structural typing rules binding base constant binders temporary
      baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent
      first substitution assignment depth temporaryDepth antecedent antecedentSorted assignmentSorted
      firstSlots firstTemporarySlots firstFresh firstTemporaryFresh firstDisjoint variableTyping constantTyping
    have secondBudget : second.binderDepth + Subst.maxBinderDepth substitution ≤
        max first.binderDepth second.binderDepth + Subst.maxBinderDepth substitution :=
      Nat.add_le_add_right (Nat.le_max_right _ _) _
    have secondSlots := fun offset smaller => slots offset (Nat.lt_of_lt_of_le smaller secondBudget)
    have secondTemporarySlots := fun offset smaller => temporarySlots offset (Nat.lt_of_lt_of_le smaller secondBudget)
    have secondFresh := fun offset smaller => fresh offset (Nat.lt_of_lt_of_le smaller secondBudget)
    have secondTemporaryFresh := fun offset smaller => temporaryFresh offset (Nat.lt_of_lt_of_le smaller secondBudget)
    have secondDisjoint := fun firstOffset firstSmaller secondOffset secondSmaller =>
      disjoint firstOffset (Nat.lt_of_lt_of_le firstSmaller secondBudget)
        secondOffset (Nat.lt_of_lt_of_le secondSmaller secondBudget)
    have secondSorted := substitution_encodings_sorted signature context base constant binders baseSorted
      constantSorted second substitution assignment depth assignmentSorted secondSlots
    let secondProof := HOLKernelSubstitution.compile signature profile structural typing rules binding base constant binders temporary
      baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent
      second substitution assignment depth temporaryDepth antecedent antecedentSorted assignmentSorted
      secondSlots secondTemporarySlots secondFresh secondTemporaryFresh secondDisjoint variableTyping constantTyping
    have firstNames := fun offset less => sourceNames offset (Nat.lt_of_lt_of_le less firstBudget)
    have firstTemporaryNames := fun offset less => temporaryNames offset (Nat.lt_of_lt_of_le less firstBudget)
    have firstDictionary := fun offset less => dictionaryFresh offset (Nat.lt_of_lt_of_le less firstBudget)
    obtain ⟨fuelFirst, ⟨treeFirst⟩⟩ := ihFirst substitution assignment depth temporaryDepth antecedent antecedentSorted assignmentSorted
      firstSlots firstTemporarySlots firstFresh firstTemporaryFresh firstDisjoint variableTyping constantTyping
      rho names nodup namesAbove assignmentEq firstNames firstTemporaryNames firstDictionary g contextRead ruleAt bindingAt
      selected structuralSelected bindingSelected
    obtain ⟨leftFirstRead, rightFirstRead⟩ := substitution_read signature abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq binders bindersInjective bindersAbove first substitution assignment depth rho names nodup namesAbove assignmentEq firstNames firstDictionary
    have secondNames := fun offset less => sourceNames offset (Nat.lt_of_lt_of_le less secondBudget)
    have secondTemporaryNames := fun offset less => temporaryNames offset (Nat.lt_of_lt_of_le less secondBudget)
    have secondDictionary := fun offset less => dictionaryFresh offset (Nat.lt_of_lt_of_le less secondBudget)
    obtain ⟨fuelSecond, ⟨treeSecond⟩⟩ := ihSecond substitution assignment depth temporaryDepth antecedent antecedentSorted assignmentSorted
      secondSlots secondTemporarySlots secondFresh secondTemporaryFresh secondDisjoint variableTyping constantTyping
      rho names nodup namesAbove assignmentEq secondNames secondTemporaryNames secondDictionary g contextRead ruleAt bindingAt
      selected structuralSelected bindingSelected
    obtain ⟨leftSecondRead, rightSecondRead⟩ := substitution_read signature abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq binders bindersInjective bindersAbove second substitution assignment depth rho names nodup namesAbove assignmentEq secondNames secondDictionary
    simpa only [HOLKernelSubstitution.compile, HOL.subst, HOL.rename] using
      HOLKernelCongruenceReadback.disjunction_admitted signature abbreviation profile distinct dictionary parameters rules binding names
        antecedent _ _ _ _ antecedentSorted firstSorted.1 firstSorted.2 secondSorted.1 secondSorted.2 firstProof secondProof g
        (HOL.rename rho (HOL.subst substitution first)) (HOL.rename rho (HOL.subst substitution first))
        (HOL.rename rho (HOL.subst substitution second)) (HOL.rename rho (HOL.subst substitution second))
        contextRead leftFirstRead rightFirstRead leftSecondRead rightSecondRead ruleAt bindingAt selected treeFirst treeSecond
  | @imp gamma first second ihFirst ihSecond =>
    intro delta substitution assignment depth temporaryDepth antecedent antecedentSorted assignmentSorted slots temporarySlots
      fresh temporaryFresh disjoint variableTyping constantTyping target rho names nodup namesAbove assignmentEq sourceNames temporaryNames
      dictionaryFresh g contextRead ruleAt bindingAt selected structuralSelected bindingSelected
    have firstBudget : first.binderDepth + Subst.maxBinderDepth substitution ≤
        max first.binderDepth second.binderDepth + Subst.maxBinderDepth substitution :=
      Nat.add_le_add_right (Nat.le_max_left _ _) _
    have firstSlots := fun offset smaller => slots offset (Nat.lt_of_lt_of_le smaller firstBudget)
    have firstTemporarySlots := fun offset smaller => temporarySlots offset (Nat.lt_of_lt_of_le smaller firstBudget)
    have firstFresh := fun offset smaller => fresh offset (Nat.lt_of_lt_of_le smaller firstBudget)
    have firstTemporaryFresh := fun offset smaller => temporaryFresh offset (Nat.lt_of_lt_of_le smaller firstBudget)
    have firstDisjoint := fun firstOffset firstSmaller secondOffset secondSmaller =>
      disjoint firstOffset (Nat.lt_of_lt_of_le firstSmaller firstBudget)
        secondOffset (Nat.lt_of_lt_of_le secondSmaller firstBudget)
    have firstSorted := substitution_encodings_sorted signature context base constant binders baseSorted
      constantSorted first substitution assignment depth assignmentSorted firstSlots
    let firstProof := HOLKernelSubstitution.compile signature profile structural typing rules binding base constant binders temporary
      baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent
      first substitution assignment depth temporaryDepth antecedent antecedentSorted assignmentSorted
      firstSlots firstTemporarySlots firstFresh firstTemporaryFresh firstDisjoint variableTyping constantTyping
    have secondBudget : second.binderDepth + Subst.maxBinderDepth substitution ≤
        max first.binderDepth second.binderDepth + Subst.maxBinderDepth substitution :=
      Nat.add_le_add_right (Nat.le_max_right _ _) _
    have secondSlots := fun offset smaller => slots offset (Nat.lt_of_lt_of_le smaller secondBudget)
    have secondTemporarySlots := fun offset smaller => temporarySlots offset (Nat.lt_of_lt_of_le smaller secondBudget)
    have secondFresh := fun offset smaller => fresh offset (Nat.lt_of_lt_of_le smaller secondBudget)
    have secondTemporaryFresh := fun offset smaller => temporaryFresh offset (Nat.lt_of_lt_of_le smaller secondBudget)
    have secondDisjoint := fun firstOffset firstSmaller secondOffset secondSmaller =>
      disjoint firstOffset (Nat.lt_of_lt_of_le firstSmaller secondBudget)
        secondOffset (Nat.lt_of_lt_of_le secondSmaller secondBudget)
    have secondSorted := substitution_encodings_sorted signature context base constant binders baseSorted
      constantSorted second substitution assignment depth assignmentSorted secondSlots
    let secondProof := HOLKernelSubstitution.compile signature profile structural typing rules binding base constant binders temporary
      baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent
      second substitution assignment depth temporaryDepth antecedent antecedentSorted assignmentSorted
      secondSlots secondTemporarySlots secondFresh secondTemporaryFresh secondDisjoint variableTyping constantTyping
    have firstNames := fun offset less => sourceNames offset (Nat.lt_of_lt_of_le less firstBudget)
    have firstTemporaryNames := fun offset less => temporaryNames offset (Nat.lt_of_lt_of_le less firstBudget)
    have firstDictionary := fun offset less => dictionaryFresh offset (Nat.lt_of_lt_of_le less firstBudget)
    obtain ⟨fuelFirst, ⟨treeFirst⟩⟩ := ihFirst substitution assignment depth temporaryDepth antecedent antecedentSorted assignmentSorted
      firstSlots firstTemporarySlots firstFresh firstTemporaryFresh firstDisjoint variableTyping constantTyping
      rho names nodup namesAbove assignmentEq firstNames firstTemporaryNames firstDictionary g contextRead ruleAt bindingAt
      selected structuralSelected bindingSelected
    obtain ⟨leftFirstRead, rightFirstRead⟩ := substitution_read signature abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq binders bindersInjective bindersAbove first substitution assignment depth rho names nodup namesAbove assignmentEq firstNames firstDictionary
    have secondNames := fun offset less => sourceNames offset (Nat.lt_of_lt_of_le less secondBudget)
    have secondTemporaryNames := fun offset less => temporaryNames offset (Nat.lt_of_lt_of_le less secondBudget)
    have secondDictionary := fun offset less => dictionaryFresh offset (Nat.lt_of_lt_of_le less secondBudget)
    obtain ⟨fuelSecond, ⟨treeSecond⟩⟩ := ihSecond substitution assignment depth temporaryDepth antecedent antecedentSorted assignmentSorted
      secondSlots secondTemporarySlots secondFresh secondTemporaryFresh secondDisjoint variableTyping constantTyping
      rho names nodup namesAbove assignmentEq secondNames secondTemporaryNames secondDictionary g contextRead ruleAt bindingAt
      selected structuralSelected bindingSelected
    obtain ⟨leftSecondRead, rightSecondRead⟩ := substitution_read signature abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq binders bindersInjective bindersAbove second substitution assignment depth rho names nodup namesAbove assignmentEq secondNames secondDictionary
    simpa only [HOLKernelSubstitution.compile, HOL.subst, HOL.rename] using
      HOLKernelCongruenceReadback.implication_admitted signature abbreviation profile distinct dictionary parameters rules binding names
        antecedent _ _ _ _ antecedentSorted firstSorted.1 firstSorted.2 secondSorted.1 secondSorted.2 firstProof secondProof g
        (HOL.rename rho (HOL.subst substitution first)) (HOL.rename rho (HOL.subst substitution first))
        (HOL.rename rho (HOL.subst substitution second)) (HOL.rename rho (HOL.subst substitution second))
        contextRead leftFirstRead rightFirstRead leftSecondRead rightSecondRead ruleAt bindingAt selected treeFirst treeSecond
  | @eq gamma operand first second ihFirst ihSecond =>
    intro delta substitution assignment depth temporaryDepth antecedent antecedentSorted assignmentSorted slots temporarySlots
      fresh temporaryFresh disjoint variableTyping constantTyping target rho names nodup namesAbove assignmentEq sourceNames temporaryNames
      dictionaryFresh g contextRead ruleAt bindingAt selected structuralSelected bindingSelected
    have firstBudget : first.binderDepth + Subst.maxBinderDepth substitution ≤
        max first.binderDepth second.binderDepth + Subst.maxBinderDepth substitution :=
      Nat.add_le_add_right (Nat.le_max_left _ _) _
    have firstSlots := fun offset smaller => slots offset (Nat.lt_of_lt_of_le smaller firstBudget)
    have firstTemporarySlots := fun offset smaller => temporarySlots offset (Nat.lt_of_lt_of_le smaller firstBudget)
    have firstFresh := fun offset smaller => fresh offset (Nat.lt_of_lt_of_le smaller firstBudget)
    have firstTemporaryFresh := fun offset smaller => temporaryFresh offset (Nat.lt_of_lt_of_le smaller firstBudget)
    have firstDisjoint := fun firstOffset firstSmaller secondOffset secondSmaller =>
      disjoint firstOffset (Nat.lt_of_lt_of_le firstSmaller firstBudget)
        secondOffset (Nat.lt_of_lt_of_le secondSmaller firstBudget)
    have firstSorted := substitution_encodings_sorted signature context base constant binders baseSorted
      constantSorted first substitution assignment depth assignmentSorted firstSlots
    let firstProof := HOLKernelSubstitution.compile signature profile structural typing rules binding base constant binders temporary
      baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent
      first substitution assignment depth temporaryDepth antecedent antecedentSorted assignmentSorted
      firstSlots firstTemporarySlots firstFresh firstTemporaryFresh firstDisjoint variableTyping constantTyping
    have secondBudget : second.binderDepth + Subst.maxBinderDepth substitution ≤
        max first.binderDepth second.binderDepth + Subst.maxBinderDepth substitution :=
      Nat.add_le_add_right (Nat.le_max_right _ _) _
    have secondSlots := fun offset smaller => slots offset (Nat.lt_of_lt_of_le smaller secondBudget)
    have secondTemporarySlots := fun offset smaller => temporarySlots offset (Nat.lt_of_lt_of_le smaller secondBudget)
    have secondFresh := fun offset smaller => fresh offset (Nat.lt_of_lt_of_le smaller secondBudget)
    have secondTemporaryFresh := fun offset smaller => temporaryFresh offset (Nat.lt_of_lt_of_le smaller secondBudget)
    have secondDisjoint := fun firstOffset firstSmaller secondOffset secondSmaller =>
      disjoint firstOffset (Nat.lt_of_lt_of_le firstSmaller secondBudget)
        secondOffset (Nat.lt_of_lt_of_le secondSmaller secondBudget)
    have secondSorted := substitution_encodings_sorted signature context base constant binders baseSorted
      constantSorted second substitution assignment depth assignmentSorted secondSlots
    let secondProof := HOLKernelSubstitution.compile signature profile structural typing rules binding base constant binders temporary
      baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent
      second substitution assignment depth temporaryDepth antecedent antecedentSorted assignmentSorted
      secondSlots secondTemporarySlots secondFresh secondTemporaryFresh secondDisjoint variableTyping constantTyping
    have firstNames := fun offset less => sourceNames offset (Nat.lt_of_lt_of_le less firstBudget)
    have firstTemporaryNames := fun offset less => temporaryNames offset (Nat.lt_of_lt_of_le less firstBudget)
    have firstDictionary := fun offset less => dictionaryFresh offset (Nat.lt_of_lt_of_le less firstBudget)
    obtain ⟨fuelFirst, ⟨treeFirst⟩⟩ := ihFirst substitution assignment depth temporaryDepth antecedent antecedentSorted assignmentSorted
      firstSlots firstTemporarySlots firstFresh firstTemporaryFresh firstDisjoint variableTyping constantTyping
      rho names nodup namesAbove assignmentEq firstNames firstTemporaryNames firstDictionary g contextRead ruleAt bindingAt
      selected structuralSelected bindingSelected
    obtain ⟨leftFirstRead, rightFirstRead⟩ := substitution_read signature abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq binders bindersInjective bindersAbove first substitution assignment depth rho names nodup namesAbove assignmentEq firstNames firstDictionary
    have secondNames := fun offset less => sourceNames offset (Nat.lt_of_lt_of_le less secondBudget)
    have secondTemporaryNames := fun offset less => temporaryNames offset (Nat.lt_of_lt_of_le less secondBudget)
    have secondDictionary := fun offset less => dictionaryFresh offset (Nat.lt_of_lt_of_le less secondBudget)
    obtain ⟨fuelSecond, ⟨treeSecond⟩⟩ := ihSecond substitution assignment depth temporaryDepth antecedent antecedentSorted assignmentSorted
      secondSlots secondTemporarySlots secondFresh secondTemporaryFresh secondDisjoint variableTyping constantTyping
      rho names nodup namesAbove assignmentEq secondNames secondTemporaryNames secondDictionary g contextRead ruleAt bindingAt
      selected structuralSelected bindingSelected
    obtain ⟨leftSecondRead, rightSecondRead⟩ := substitution_read signature abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq binders bindersInjective bindersAbove second substitution assignment depth rho names nodup namesAbove assignmentEq secondNames secondDictionary
    simpa only [HOLKernelSubstitution.compile, HOL.subst, HOL.rename] using
      HOLKernelCongruenceReadback.equality_admitted signature abbreviation profile distinct dictionary parameters rules binding names
        antecedent (encodeType signature.symbol base operand) _ _ _ _ antecedentSorted (encodeType_sorted signature context base baseSorted operand) firstSorted.1 firstSorted.2 secondSorted.1 secondSorted.2 firstProof secondProof g
        (HOL.rename rho (HOL.subst substitution first)) (HOL.rename rho (HOL.subst substitution first))
        (HOL.rename rho (HOL.subst substitution second)) (HOL.rename rho (HOL.subst substitution second))
        (typeRead operand) contextRead leftFirstRead rightFirstRead leftSecondRead rightSecondRead ruleAt bindingAt selected treeFirst treeSecond
  | @not gamma body ih =>
    intro delta substitution assignment depth temporaryDepth antecedent antecedentSorted assignmentSorted slots temporarySlots
      fresh temporaryFresh disjoint variableTyping constantTyping target rho names nodup namesAbove assignmentEq sourceNames temporaryNames
      dictionaryFresh g contextRead ruleAt bindingAt selected structuralSelected bindingSelected
    have formed := substitution_encodings_sorted signature context base constant binders baseSorted constantSorted
      body substitution assignment depth assignmentSorted slots
    let child := HOLKernelSubstitution.compile signature profile structural typing rules binding base constant binders temporary
      baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent body substitution assignment depth
      temporaryDepth antecedent antecedentSorted assignmentSorted slots temporarySlots fresh temporaryFresh disjoint variableTyping constantTyping
    obtain ⟨fuel, ⟨tree⟩⟩ := ih substitution assignment depth temporaryDepth antecedent antecedentSorted assignmentSorted slots temporarySlots
      fresh temporaryFresh disjoint variableTyping constantTyping rho names nodup namesAbove assignmentEq sourceNames temporaryNames dictionaryFresh
      g contextRead ruleAt bindingAt selected structuralSelected bindingSelected
    obtain ⟨leftRead, rightRead⟩ := substitution_read signature abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq binders bindersInjective bindersAbove body substitution assignment depth rho names nodup namesAbove assignmentEq sourceNames dictionaryFresh
    refine ⟨max 1 fuel + 2, ?_⟩
    simpa only [HOLKernelSubstitution.compile, HOL.subst, HOL.rename] using
      HOLKernelCongruenceReadback.negation_admitted signature abbreviation profile distinct dictionary parameters rules names antecedent _ _
        antecedentSorted formed.1 formed.2 child g (HOL.rename rho (HOL.subst substitution body)) (HOL.rename rho (HOL.subst substitution body))
        contextRead leftRead rightRead ruleAt bindingAt (selected .applicationArgument) tree
  | @lam domain gamma result body ih | @all domain gamma body ih | @ex domain gamma body ih =>
    intro delta substitution assignment depth temporaryDepth antecedent antecedentSorted assignmentSorted slots temporarySlots
      fresh temporaryFresh disjoint variableTyping constantTyping target rho names nodup namesAbove assignmentEq sourceNames temporaryNames
      dictionaryFresh g contextRead ruleAt bindingAt selected structuralSelected bindingSelected
    simp only [Term.binderDepth] at slots temporarySlots fresh temporaryFresh disjoint
    have head : context[binders depth]? = some (.bound signature.ids.object) := by
      have found := slots 0 (by omega)
      simpa only [Nat.add_zero] using found
    have domainSorted := encodeType_sorted signature context base baseSorted domain
    have headSorted : Preterm.HasType terms context (.var (binders depth)) [] signature.ids.object :=
      .var (binder := .bound signature.ids.object) head
    let extra := hasType signature.symbol (.var (binders depth)) (encodeType signature.symbol base domain)
    let extended := conjunction signature.symbol antecedent extra
    have extraSorted := hasType_sorted signature context headSorted domainSorted
    have extendedSorted := conjunction_sorted signature context antecedentSorted extraSorted
    have bodySlots : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.lift (σ := domain) substitution),
        context[binders (depth + 1 + offset)]? = some (.bound signature.ids.object) := by
      intro offset smaller
      rw [Subst.maxBinderDepth_lift] at smaller
      have found := slots (offset + 1) (by omega)
      simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using found
    have bodyTemporarySlots : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.lift (σ := domain) substitution),
        context[temporary (temporaryDepth + 1 + offset)]? = some (.bound signature.ids.object) := by
      intro offset smaller
      rw [Subst.maxBinderDepth_lift] at smaller
      have found := temporarySlots (offset + 1) (by omega)
      simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using found
    have bodyFresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.lift (σ := domain) substitution),
        ¬ Preterm.HasVar context (binders (depth + 1 + offset)) extended := by
      intro offset smaller
      rw [Subst.maxBinderDepth_lift] at smaller
      apply contextExtension_independent context _ _ signature.ids.object signature.symbol _ _ head
      · intro same
        have impossible := bindersInjective same
        omega
      · have independent := fresh (offset + 1) (by omega)
        simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using independent
      · exact encodeType_independent context _ signature.symbol base (baseIndependent _) domain
    have bodyTemporaryFresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.lift (σ := domain) substitution),
        ¬ Preterm.HasVar context (temporary (temporaryDepth + 1 + offset)) extended := by
      intro offset smaller
      rw [Subst.maxBinderDepth_lift] at smaller
      apply contextExtension_independent context _ _ signature.ids.object signature.symbol _ _ head
      · have apart := Ne.symm (disjoint 0 (by omega) (offset + 1) (by omega))
        simpa only [Nat.add_zero, Nat.add_assoc, Nat.add_comm 1 offset] using apart
      · have independent := temporaryFresh (offset + 1) (by omega)
        simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using independent
      · exact encodeType_independent context _ signature.symbol base (temporaryIndependent _) domain
    have bodyDisjoint : ∀ firstOffset < body.binderDepth + Subst.maxBinderDepth (Subst.lift (σ := domain) substitution),
        ∀ secondOffset < body.binderDepth + Subst.maxBinderDepth (Subst.lift (σ := domain) substitution),
          binders (depth + 1 + firstOffset) ≠ temporary (temporaryDepth + 1 + secondOffset) := by
      intro firstOffset firstSmaller secondOffset secondSmaller
      rw [Subst.maxBinderDepth_lift] at firstSmaller secondSmaller
      have apart := disjoint (firstOffset + 1) (by omega) (secondOffset + 1) (by omega)
      simpa only [Nat.add_assoc, Nat.add_comm 1 firstOffset, Nat.add_comm 1 secondOffset] using apart
    have extendedTargetSorted : ∀ {type} (index : Var (domain :: delta) type),
        Preterm.HasType terms context (Assignment.extend (.var (binders depth)) assignment index)
          [] signature.ids.object :=
      Assignment.extend_sorted signature context _ assignment headSorted assignmentSorted
    let extendedVariables : ∀ {type} (index : Var (domain :: delta) type),
        CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
          (context := context) (hypotheses := [])
          (typed signature.symbol extended (Assignment.extend (.var (binders depth)) assignment index)
            (encodeType signature.symbol base type)) := by
      intro type index
      cases index with
      | vz => exact HOLKernelStructuralRules.right signature structural antecedent extra antecedentSorted extraSorted
      | vs index =>
          exact (HOLKernelTermTyping.weakenVariables signature structural base assignment antecedent extra
            antecedentSorted extraSorted baseSorted assignmentSorted variableTyping) index
    let extendedConstants : ∀ {type} (symbol : Const type),
        CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
          (context := context) (hypotheses := [])
          (typed signature.symbol extended (constant symbol) (encodeType signature.symbol base type)) :=
      HOLKernelTermTyping.weakenConstants signature structural base constant antecedent extra
        antecedentSorted extraSorted baseSorted constantSorted constantTyping
    have leftImages : ∀ {type} (index : Var gamma type),
        Preterm.HasType terms context
          (encodeSubstitution signature.symbol base constant binders assignment depth substitution index)
          [] signature.ids.object :=
      encodeSubstitution_sorted signature context base constant binders baseSorted constantSorted substitution
        assignment depth assignmentSorted (fun offset smaller => slots offset (by omega))
    have rightImages : ∀ {type} (index : Var gamma type),
        Preterm.HasType terms context
          (encodeSubstitution signature.symbol base constant binders assignment (depth + 1) substitution index)
          [] signature.ids.object := by
      apply encodeSubstitution_sorted signature context base constant binders baseSorted constantSorted substitution
        assignment (depth + 1) assignmentSorted
      intro offset smaller
      have found := slots (offset + 1) (by omega)
      simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using found
    let imageEquations : ∀ {type} (index : Var gamma type),
        CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
          (context := context) (hypotheses := [])
          (entails signature.symbol extended (holds signature.symbol
            (equality signature.symbol (encodeType signature.symbol base type)
              (encodeSubstitution signature.symbol base constant binders assignment depth substitution index)
              (encodeSubstitution signature.symbol base constant binders assignment (depth + 1) substitution index)))) := by
      intro type index
      have heightBound := Subst.binderDepth_le_maxBinderDepth substitution index
      let renamed := HOLKernelAlpha.rebind signature profile structural typing rules binding base constant binders temporary
        baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent
        (substitution index) assignment depth (depth + 1) temporaryDepth antecedent antecedentSorted assignmentSorted
        (fun offset smaller => slots offset (by omega))
        (by
          intro offset smaller
          have found := slots (offset + 1) (by omega)
          simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using found)
        (fun offset smaller => temporarySlots offset (by omega))
        (fun offset smaller => fresh offset (by omega))
        (by
          intro offset smaller
          have independent := fresh (offset + 1) (by omega)
          simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using independent)
        (fun offset smaller => temporaryFresh offset (by omega))
        (by intro first firstSmaller second secondSmaller; exact disjoint first (by omega) second (by omega))
        (by
          intro first firstSmaller second secondSmaller
          have apart := Ne.symm (disjoint (second + 1) (by omega) first (by omega))
          simpa only [Nat.add_assoc, Nat.add_comm 1 second] using apart)
        variableTyping constantTyping
      exact HOLKernelStructuralRules.weaken signature structural antecedent extra _ antecedentSorted extraSorted
        (holds_sorted signature context (signature.application context .eqc _
          (.cons (.regular (encodeType_sorted signature context base baseSorted type))
            (.cons (.regular (leftImages index)) (.cons (.regular (rightImages index)) .nil))))) renamed
    let leftAssignment : Assignment (domain :: gamma) := Assignment.extend (.var (binders depth))
      (encodeSubstitution signature.symbol base constant binders assignment depth substitution)
    let rightAssignment : Assignment (domain :: gamma) := Assignment.extend (.var (binders depth))
      (encodeSubstitution signature.symbol base constant binders assignment (depth + 1) substitution)
    have leftAssignmentSorted : ∀ {type} (index : Var (domain :: gamma) type),
        Preterm.HasType terms context (leftAssignment index) [] signature.ids.object :=
      Assignment.extend_sorted signature context _ _ headSorted leftImages
    have rightAssignmentSorted : ∀ {type} (index : Var (domain :: gamma) type),
        Preterm.HasType terms context (rightAssignment index) [] signature.ids.object :=
      Assignment.extend_sorted signature context _ _ headSorted rightImages
    let related : ∀ {type} (index : Var (domain :: gamma) type),
        CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
          (context := context) (hypotheses := [])
          (entails signature.symbol extended (holds signature.symbol
            (equality signature.symbol (encodeType signature.symbol base type)
              (leftAssignment index) (rightAssignment index)))) := by
      intro type index
      cases index with
      | vz =>
          exact HOLKernelInferenceProofs.Native.reflexivity signature rules extended _ _ extendedSorted
            domainSorted headSorted
            (HOLKernelStructuralRules.right signature structural antecedent extra antecedentSorted extraSorted)
      | vs index => exact imageEquations index

    let bodyType : Ty Unit := (fun {type} (_ : Term Const (domain :: gamma) type) => type) body
    let nextNames : Names (domain :: target) := BinderNames.cons (binders depth) names
    let shiftedRho : Rename Unit delta (domain :: target) := fun index => Var.vs (rho index)
    let meaning : Subst Const (domain :: gamma) (domain :: target) :=
      fun index => HOL.rename (Rename.lift rho) (Subst.lift substitution index)
    have headNotMem : binders depth ∉ names.toList := by
      simpa only [Nat.add_zero] using sourceNames 0 (by simp only [Term.binderDepth]; omega)
    have headFresh : names.lookup? (binders depth) = none := BinderNames.lookup?_none_of_not_mem names headNotMem
    have headDictionary : dictionary (binders depth) = none := by
      simpa only [Nat.add_zero] using dictionaryFresh 0 (by simp only [Term.binderDepth]; omega)
    have nextLookup : LookupPreserving dictionary (Rename.weaken (σ := domain)) names nextNames :=
      LookupPreserving.weaken dictionary names domain (binders depth) headFresh headDictionary
    have nextNodup : nextNames.toList.Nodup := List.nodup_cons.mpr ⟨headNotMem, nodup⟩
    have nextAbove : ∀ name ∈ nextNames.toList, parameters ≤ name := by
      intro name member
      rcases List.mem_cons.mp member with rfl | member
      · exact bindersAbove depth
      · exact namesAbove _ member
    have shiftedAssignment : ∀ {type} (index : Var delta type), assignment index = .var (nextNames.nameOf (shiftedRho index)) := by
      intro type index
      simpa only [nextNames, shiftedRho, BinderNames.nameOf] using assignmentEq index
    have nextAssignment : ∀ {type} (index : Var (domain :: delta) type),
        Assignment.extend (.var (binders depth)) assignment index = .var (nextNames.nameOf (Rename.lift rho index)) := by
      intro type index
      cases index with
      | vz => rfl
      | vs index => exact assignmentEq index
    have nextSourceNames : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.lift (σ := domain) substitution),
        binders (depth + 1 + offset) ∉ nextNames.toList := by
      intro offset less member
      rw [Subst.maxBinderDepth_lift] at less
      rcases List.mem_cons.mp member with same | member
      · have impossible := bindersInjective same
        omega
      · have absent := sourceNames (offset + 1) (by simp only [Term.binderDepth]; omega)
        exact absent (by simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using member)
    have nextTemporaryNames : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.lift (σ := domain) substitution),
        temporary (temporaryDepth + 1 + offset) ∉ nextNames.toList := by
      intro offset less member
      rw [Subst.maxBinderDepth_lift] at less
      rcases List.mem_cons.mp member with same | member
      · have apart := disjoint 0 (by omega) (offset + 1) (by omega)
        exact apart (by simpa only [Nat.add_zero, Nat.add_assoc, Nat.add_comm 1 offset] using same.symm)
      · have absent := temporaryNames (offset + 1) (by simp only [Term.binderDepth]; omega)
        exact absent (by simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using member)
    have nextDictionary : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.lift (σ := domain) substitution),
        dictionary (binders (depth + 1 + offset)) = none := by
      intro offset less
      rw [Subst.maxBinderDepth_lift] at less
      simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using dictionaryFresh (offset + 1) (by simp only [Term.binderDepth]; omega)
    have oldContextRead := logical_judgment_rename_of_read profile dictionary parameters names nextNames Rename.weaken nextLookup
      (expandEquivalence signature.symbol abbreviation.reference antecedent) g contextRead
    have headRead : HOLKernelLogicalFunctionReadback.reader profile dictionary parameters nextNames (.var (binders depth)) =
        some ⟨domain, Term.var .vz⟩ := by
      simp [HOLKernelLogicalFunctionReadback.reader, readTermWith, readVariable, nextNames]
    have extraRead : readJudgmentWith (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) signature.symbol nextNames
        (expandEquivalence signature.symbol abbreviation.reference extra) = some (.typing (Term.var .vz : Term Const (domain :: target) domain)) := by
      simp [extra, hasType, applySymbol, Preterm.applyArgs, expandEquivalence, distinct, readJudgmentWith,
        readHead_reference signature.symbol signature.symbol_injective, readTypingWith, typeRead domain, headRead, expect_same]
    let nextG : Judgment Const (domain :: target) := .conjunction (g.rename Rename.weaken) (.typing (.var .vz))
    have nextContextRead : readJudgmentWith (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) signature.symbol nextNames
        (expandEquivalence signature.symbol abbreviation.reference extended) = some nextG := by
      simp [extended, conjunction, applySymbol, Preterm.applyArgs, expandEquivalence, distinct, readJudgmentWith,
        readHead_reference signature.symbol signature.symbol_injective, oldContextRead, extraRead, nextG]
    have meaning_vs {type} (index : Var gamma type) : meaning (.vs index) = HOL.rename shiftedRho (substitution index) := by
      simp only [meaning, Subst.lift, rename_comp, Rename.weaken, Rename.lift, shiftedRho]
    have imageLeftRead : ∀ {type} (index : Var gamma type),
        HOLKernelLogicalFunctionReadback.reader profile dictionary parameters nextNames
          (expandEquivalence signature.symbol abbreviation.reference
            (encodeSubstitution signature.symbol base constant binders assignment depth substitution index)) =
        some ⟨type, HOL.rename shiftedRho (substitution index)⟩ := by
      intro type index
      exact HOLKernelAlphaReadback.encoded_read abbreviation profile distinct dictionary indices parameters lookup bounded
        base constant baseEq constantEq shiftedRho nextNames assignment shiftedAssignment binders bindersInjective bindersAbove
        (substitution index) depth nextNodup nextAbove
        (by
          intro offset less type sourceIndex
          change binders (depth + offset) ≠ names.nameOf (rho sourceIndex)
          exact BinderNames.ne_nameOf_of_not_mem names
            (sourceNames offset (by have h := Subst.binderDepth_le_maxBinderDepth substitution index; simp only [Term.binderDepth]; omega)) (rho sourceIndex))
    have imageRightRead : ∀ {type} (index : Var gamma type),
        HOLKernelLogicalFunctionReadback.reader profile dictionary parameters nextNames
          (expandEquivalence signature.symbol abbreviation.reference
            (encodeSubstitution signature.symbol base constant binders assignment (depth + 1) substitution index)) =
        some ⟨type, HOL.rename shiftedRho (substitution index)⟩ := by
      intro type index
      exact HOLKernelAlphaReadback.encoded_read abbreviation profile distinct dictionary indices parameters lookup bounded
        base constant baseEq constantEq shiftedRho nextNames assignment shiftedAssignment binders bindersInjective bindersAbove
        (substitution index) (depth + 1) nextNodup nextAbove
        (by
          intro offset less type sourceIndex
          change binders (depth + 1 + offset) ≠ names.nameOf (rho sourceIndex)
          have absent := sourceNames (offset + 1) (by have h := Subst.binderDepth_le_maxBinderDepth substitution index; simp only [Term.binderDepth]; omega)
          apply BinderNames.ne_nameOf_of_not_mem names
          simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using absent)
    have leftAssignmentFixed : ∀ {type} (index : Var (domain :: gamma) type),
        expandEquivalence signature.symbol abbreviation.reference (leftAssignment index) = leftAssignment index := by
      intro type index
      cases index with
      | vz => simp [leftAssignment, Assignment.extend, expandEquivalence]
      | vs index =>
          exact encoded_fixed signature abbreviation distinct base constant baseEq indices constantEq
            binders rho names assignment assignmentEq (substitution index) depth
    have leftAssignmentRead : ∀ {type} (index : Var (domain :: gamma) type),
        HOLKernelLogicalFunctionReadback.reader profile dictionary parameters nextNames (leftAssignment index) = some ⟨type, meaning index⟩ := by
      intro type index
      cases index with
      | vz => simpa only [leftAssignment, Assignment.extend, meaning, Subst.lift, HOL.rename, Rename.lift] using headRead
      | vs index =>
          have reading := imageLeftRead index
          change HOLKernelLogicalFunctionReadback.reader profile dictionary parameters nextNames
            (expandEquivalence signature.symbol abbreviation.reference (leftAssignment (.vs index))) = _ at reading
          rw [leftAssignmentFixed] at reading
          simpa only [meaning_vs] using reading
    have rightAssignmentFixed : ∀ {type} (index : Var (domain :: gamma) type),
        expandEquivalence signature.symbol abbreviation.reference (rightAssignment index) = rightAssignment index := by
      intro type index
      cases index with
      | vz => simp [rightAssignment, Assignment.extend, expandEquivalence]
      | vs index =>
          exact encoded_fixed signature abbreviation distinct base constant baseEq indices constantEq
            binders rho names assignment assignmentEq (substitution index) (depth + 1)
    have rightAssignmentRead : ∀ {type} (index : Var (domain :: gamma) type),
        HOLKernelLogicalFunctionReadback.reader profile dictionary parameters nextNames (rightAssignment index) = some ⟨type, meaning index⟩ := by
      intro type index
      cases index with
      | vz => simpa only [rightAssignment, Assignment.extend, meaning, Subst.lift, HOL.rename, Rename.lift] using headRead
      | vs index =>
          have reading := imageRightRead index
          change HOLKernelLogicalFunctionReadback.reader profile dictionary parameters nextNames
            (expandEquivalence signature.symbol abbreviation.reference (rightAssignment (.vs index))) = _ at reading
          rw [rightAssignmentFixed] at reading
          simpa only [meaning_vs] using reading
    have imageAdmission : ∀ {type} (index : Var gamma type),
        AdmissionUnderRenaming (context := context) abbreviation profile dictionary parameters ruleAt bindingAt nextNames
          (imageEquations index).val (.imp nextG.formula (.eq (meaning (.vs index)) (meaning (.vs index)))) := by
      intro type index
      have heightBound := Subst.binderDepth_le_maxBinderDepth substitution index
      let renamed := HOLKernelAlpha.rebind signature profile structural typing rules binding base constant binders temporary
        baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent
        (substitution index) assignment depth (depth + 1) temporaryDepth antecedent antecedentSorted assignmentSorted
        (fun offset smaller => slots offset (by omega))
        (by
          intro offset smaller
          have found := slots (offset + 1) (by omega)
          simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using found)
        (fun offset smaller => temporarySlots offset (by omega))
        (fun offset smaller => fresh offset (by omega))
        (by
          intro offset smaller
          have independent := fresh (offset + 1) (by omega)
          simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using independent)
        (fun offset smaller => temporaryFresh offset (by omega))
        (by intro first firstSmaller second secondSmaller; exact disjoint first (by omega) second (by omega))
        (by
          intro first firstSmaller second secondSmaller
          have apart := Ne.symm (disjoint (second + 1) (by omega) first (by omega))
          simpa only [Nat.add_assoc, Nat.add_comm 1 second] using apart)
        variableTyping constantTyping
    -- Each image's existing alpha receipt is stable in the extended reader frame.
      have stable : AdmissionUnderRenaming (context := context) abbreviation profile dictionary parameters ruleAt bindingAt nextNames
          renamed.val (.imp (g.rename Rename.weaken).formula
            (.eq (HOL.rename shiftedRho (substitution index)) (HOL.rename shiftedRho (substitution index)))) :=
        HOLKernelAlphaReadback.rebind_admission_under_renaming signature abbreviation profile structural typing rules binding
        distinct dictionary indices parameters lookup bounded base constant baseEq constantEq binders temporary
        baseSorted constantSorted bindersInjective temporaryInjective bindersAbove temporaryAbove baseIndependent temporaryIndependent
        (substitution index) assignment depth (depth + 1) temporaryDepth antecedent antecedentSorted assignmentSorted
        (fun offset smaller => slots offset (by omega))
        (by
          intro offset smaller
          have found := slots (offset + 1) (by omega)
          simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using found)
        (fun offset smaller => temporarySlots offset (by omega))
        (fun offset smaller => fresh offset (by omega))
        (by
          intro offset smaller
          have independent := fresh (offset + 1) (by omega)
          simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using independent)
        (fun offset smaller => temporaryFresh offset (by omega))
        (by intro first firstSmaller second secondSmaller; exact disjoint first (by omega) second (by omega))
        (by
          intro first firstSmaller second secondSmaller
          have apart := Ne.symm (disjoint (second + 1) (by omega) first (by omega))
          simpa only [Nat.add_assoc, Nat.add_comm 1 second] using apart)
        variableTyping constantTyping shiftedRho nextNames nextNodup shiftedAssignment
        (by
          intro offset less type sourceIndex
          change binders (depth + offset) ≠ names.nameOf (rho sourceIndex)
          exact BinderNames.ne_nameOf_of_not_mem names (sourceNames offset (by simp only [Term.binderDepth]; omega)) (rho sourceIndex))
        (by
          intro offset less type sourceIndex
          change binders (depth + 1 + offset) ≠ names.nameOf (rho sourceIndex)
          apply BinderNames.ne_nameOf_of_not_mem names
          simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using sourceNames (offset + 1) (by simp only [Term.binderDepth]; omega))
        (by
          intro offset less type sourceIndex
          change temporary (temporaryDepth + offset) ≠ names.nameOf (rho sourceIndex)
          exact BinderNames.ne_nameOf_of_not_mem names (temporaryNames offset (by simp only [Term.binderDepth]; omega)) (rho sourceIndex))
        (g.rename Rename.weaken) oldContextRead ruleAt bindingAt selected (bindingSelected .abstractionRenaming)
      have equationRead := HOLKernelCongruenceReadback.equation_judgment_read signature abbreviation profile distinct dictionary parameters nextNames
        (encodeType signature.symbol base type) _ _ (HOL.rename shiftedRho (substitution index)) (HOL.rename shiftedRho (substitution index))
        (typeRead type) (imageLeftRead index) (imageRightRead index)
      have lifted : AdmissionUnderRenaming (context := context) abbreviation profile dictionary parameters ruleAt bindingAt nextNames
          (HOLKernelStructuralRules.weaken signature structural antecedent extra _ antecedentSorted extraSorted
            (holds_sorted signature context (signature.application context .eqc _
              (.cons (.regular (encodeType_sorted signature context base baseSorted type))
                (.cons (.regular (leftImages index)) (.cons (.regular (rightImages index)) .nil))))) renamed).val
          (.imp (.and (g.rename Rename.weaken).formula .top)
            (.eq (HOL.rename shiftedRho (substitution index)) (HOL.rename shiftedRho (substitution index)))) :=
        HOLKernelStructuralReadback.weaken_admission_under_renaming signature abbreviation profile distinct dictionary parameters
        structural nextNames antecedent extra _ antecedentSorted extraSorted
        (holds_sorted signature context (signature.application context .eqc _
          (.cons (.regular (encodeType_sorted signature context base baseSorted type))
            (.cons (.regular (leftImages index)) (.cons (.regular (rightImages index)) .nil))))) renamed
        (g.rename Rename.weaken) (.typing (.var .vz)) (.assertion (.eq (HOL.rename shiftedRho (substitution index)) (HOL.rename shiftedRho (substitution index))))
        oldContextRead extraRead equationRead ruleAt bindingAt structuralSelected stable
      have witnessEq : (imageEquations index).val =
          (HOLKernelStructuralRules.weaken signature structural antecedent extra _ antecedentSorted extraSorted
            (holds_sorted signature context (signature.application context .eqc _
              (.cons (.regular (encodeType_sorted signature context base baseSorted type))
                (.cons (.regular (leftImages index)) (.cons (.regular (rightImages index)) .nil))))) renamed).val := by rfl
      rw [witnessEq]
      intro futureContext futureRho future futureNodup futureAbove preserved
      simpa only [nextG, Judgment.formula, meaning_vs] using
        lifted futureRho future futureNodup futureAbove preserved
    have relatedAdmission : ∀ {type} (index : Var (domain :: gamma) type),
        AdmissionUnderRenaming (context := context) abbreviation profile dictionary parameters ruleAt bindingAt nextNames
          (related index).val (.imp nextG.formula (.eq (meaning index) (meaning index))) := by
      intro type index
      cases index with
      | vz =>
          intro futureContext futureRho future futureNodup futureAbove preserved
          have futureG := logical_judgment_rename_of_read profile dictionary parameters nextNames future futureRho preserved
            (expandEquivalence signature.symbol abbreviation.reference extended) nextG nextContextRead
          have futureHead := logical_reader_rename_of_read profile dictionary parameters nextNames future futureRho preserved _
            (Term.var .vz : Term Const (domain :: target) domain) headRead
          have witnessEq : (related (Var.vz : Var (domain :: gamma) domain)).val =
              (HOLKernelInferenceProofs.Native.reflexivity (definitions := definitions) (hypotheses := []) signature rules extended _ _ extendedSorted
                domainSorted headSorted (HOLKernelStructuralRules.right signature structural antecedent extra antecedentSorted extraSorted)).val := by rfl
          refine ⟨2, ?_⟩
          rw [witnessEq]
          simpa only [meaning, Subst.lift, HOL.rename, Rename.lift, Judgment.rename_formula] using
            HOLKernelCongruenceReadback.reflexivity_admitted signature abbreviation profile distinct dictionary parameters rules future
              extended (encodeType signature.symbol base domain) (.var (binders depth)) extendedSorted domainSorted headSorted
              (HOLKernelStructuralRules.right signature structural antecedent extra antecedentSorted extraSorted)
              (nextG.rename futureRho) (Term.var (futureRho .vz)) futureG (typeRead domain)
              (by simpa only [expandEquivalence, HOL.rename] using futureHead) ruleAt bindingAt (selected .reflexivity)
      | vs index =>
          have witnessEq : (related (Var.vs index)).val = (imageEquations index).val := by rfl
          rw [witnessEq]
          intro futureContext futureRho future futureNodup futureAbove preserved
          exact imageAdmission index futureRho future futureNodup futureAbove preserved
    have nextConstantsAbsent : ∀ {type} (symbol : Const type), nextNames.lookup? (indices symbol) = none := by
      intro type symbol
      apply BinderNames.lookup?_none_of_not_mem
      intro member
      have lower := nextAbove _ member
      have upper := bounded symbol
      omega
    let assignmentComparison := HOLKernelTermCongruence.congruence signature profile structural typing rules binding
      base constant binders baseSorted constantSorted bindersInjective baseIndependent body
      leftAssignment rightAssignment (depth + 1) extended extendedSorted leftAssignmentSorted rightAssignmentSorted
      (fun offset smaller => bodySlots offset (by omega))
      (fun offset smaller => bodyFresh offset (by omega)) related extendedConstants
    obtain ⟨assignmentFuel, ⟨assignmentTree⟩⟩ := HOLKernelTermCongruenceReadback.congruence_admitted signature abbreviation profile structural typing rules binding
      distinct dictionary indices parameters lookup bounded base constant baseEq constantEq binders baseSorted constantSorted
      bindersInjective bindersAbove baseIndependent body leftAssignment rightAssignment (depth + 1) extended extendedSorted
      leftAssignmentSorted rightAssignmentSorted
      (fun offset smaller => bodySlots offset (by omega))
      (fun offset smaller => bodyFresh offset (by omega)) related extendedConstants meaning meaning nextNames nextNodup nextAbove
      leftAssignmentRead rightAssignmentRead leftAssignmentFixed rightAssignmentFixed nextConstantsAbsent
      (fun offset less => BinderNames.lookup?_none_of_not_mem nextNames (nextSourceNames offset (by omega)))
      (fun offset less => nextDictionary offset (by omega)) nextG nextContextRead ruleAt bindingAt selected structuralSelected
      (bindingSelected .abstractionCongruence) relatedAdmission
    let recursiveComparison := HOLKernelSubstitution.compile signature profile structural typing rules binding base constant binders temporary
      baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent body
      (Subst.lift substitution) (Assignment.extend (.var (binders depth)) assignment)
      (depth + 1) (temporaryDepth + 1) extended extendedSorted extendedTargetSorted
      bodySlots bodyTemporarySlots bodyFresh bodyTemporaryFresh bodyDisjoint extendedVariables extendedConstants
    let substitutionComparison := by
      have value := recursiveComparison
      simp only [encodeSubstitution_lift] at value
      exact value
    obtain ⟨recursiveFuel, ⟨recursiveTree⟩⟩ := ih (Subst.lift substitution) (Assignment.extend (.var (binders depth)) assignment)
      (depth + 1) (temporaryDepth + 1) extended extendedSorted extendedTargetSorted bodySlots bodyTemporarySlots
      bodyFresh bodyTemporaryFresh bodyDisjoint extendedVariables extendedConstants (Rename.lift rho) nextNames nextNodup nextAbove
      nextAssignment nextSourceNames nextTemporaryNames nextDictionary nextG nextContextRead ruleAt bindingAt selected structuralSelected bindingSelected
    have leftBodySorted := encode_sorted signature context base constant binders baseSorted constantSorted body
      leftAssignment (depth + 1) leftAssignmentSorted (fun offset smaller => bodySlots offset (by omega))
    have middleBodySorted := encode_sorted signature context base constant binders baseSorted constantSorted body
      rightAssignment (depth + 1) rightAssignmentSorted (fun offset smaller => bodySlots offset (by omega))
    have rightBodySorted := (substitution_encodings_sorted signature context base constant binders baseSorted constantSorted
      body (Subst.lift substitution) (Assignment.extend (.var (binders depth)) assignment) (depth + 1) extendedTargetSorted bodySlots).2
    let bodyEquality := HOLKernelInferenceProofs.Native.transitivity signature rules extended _ _ _ _ extendedSorted
      (encodeType_sorted signature context base baseSorted _) leftBodySorted middleBodySorted rightBodySorted assignmentComparison substitutionComparison
    let abstractionEquality := HOLKernelBindingProofs.Native.abstractionCongruence signature binding
      antecedent (encodeType signature.symbol base domain) _ (binders depth) _ _ antecedentSorted domainSorted
      (encodeType_sorted signature context base baseSorted _) head leftBodySorted rightBodySorted
      (by simpa only [Nat.add_zero] using fresh 0 (by omega))
      (encodeType_independent context _ signature.symbol base (baseIndependent depth) domain)
      (encodeType_independent context _ signature.symbol base (baseIndependent depth) _) bodyEquality
    have bodyMeaning : HOL.subst meaning body = HOL.rename (Rename.lift rho) (HOL.subst (Subst.lift substitution) body) := by
      exact (rename_subst (Rename.lift rho) (Subst.lift substitution) body).symm
    have leftBodyRead := HOLKernelTermCongruenceReadback.assigned_read signature abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq binders bindersInjective bindersAbove body meaning leftAssignment nextNames (depth + 1)
      leftAssignmentRead leftAssignmentFixed nextConstantsAbsent
      (fun offset less => BinderNames.lookup?_none_of_not_mem nextNames (nextSourceNames offset (by omega)))
      (fun offset less => nextDictionary offset (by omega))
    have middleBodyRead := HOLKernelTermCongruenceReadback.assigned_read signature abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq binders bindersInjective bindersAbove body meaning rightAssignment nextNames (depth + 1)
      rightAssignmentRead rightAssignmentFixed nextConstantsAbsent
      (fun offset less => BinderNames.lookup?_none_of_not_mem nextNames (nextSourceNames offset (by omega)))
      (fun offset less => nextDictionary offset (by omega))
    obtain ⟨_, rightBodyRead⟩ := substitution_read signature abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq binders bindersInjective bindersAbove body (Subst.lift substitution)
      (Assignment.extend (.var (binders depth)) assignment) (depth + 1) (Rename.lift rho) nextNames nextNodup nextAbove nextAssignment
      nextSourceNames nextDictionary
    have comparisonVal : substitutionComparison.val = recursiveComparison.val := by
      simp only [substitutionComparison]
      exact CheckedProof.val_mpr
        (fun imageAssignment => entails signature.symbol extended (holds signature.symbol
          (equality signature.symbol (encodeType signature.symbol base bodyType)
            (encodeWithAssignment signature.symbol base constant binders imageAssignment (depth + 1) body)
            (encodeWithAssignment signature.symbol base constant binders (Assignment.extend (.var (binders depth)) assignment)
              (depth + 1) (HOL.subst (Subst.lift substitution) body)))))
        (encodeSubstitution_lift signature.symbol base constant binders assignment (depth + 1) (binders depth) substitution).symm recursiveComparison
    have recursiveAdmitted : AdmittedProof abbreviation theorems context (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters)
        parameters ruleAt bindingAt recursiveFuel nextNames substitutionComparison.val
        (.imp nextG.formula (.eq (HOL.subst meaning body) (HOL.subst meaning body))) := by
      rw [comparisonVal, bodyMeaning]
      exact recursiveTree
    obtain ⟨bodyTree⟩ := HOLKernelCongruenceReadback.transitivity_admitted signature abbreviation profile distinct dictionary parameters rules
      nextNames extended _ _ _ _ extendedSorted (encodeType_sorted signature context base baseSorted _) leftBodySorted middleBodySorted
      rightBodySorted assignmentComparison substitutionComparison nextG (HOL.subst meaning body) (HOL.subst meaning body) (HOL.subst meaning body)
      nextContextRead (typeRead _) leftBodyRead middleBodyRead (by rw [bodyMeaning]; exact rightBodyRead)
      ruleAt bindingAt (selected .transitivity) assignmentTree recursiveAdmitted
    obtain ⟨leftLambdaRead, rightLambdaRead⟩ := substitution_read signature abbreviation profile distinct dictionary indices parameters lookup bounded
      base constant baseEq constantEq binders bindersInjective bindersAbove (Term.lam body) substitution assignment depth rho names nodup namesAbove
      assignmentEq sourceNames dictionaryFresh
    have lambdaEquationRead := HOLKernelCongruenceReadback.equation_read signature abbreviation profile distinct dictionary parameters names
      (encodeType signature.symbol base (domain ⇒ bodyType)) _ _
      (Term.lam (HOL.subst meaning body)) (Term.lam (HOL.subst meaning body)) (typeRead _) 
      (by simpa only [HOL.subst, HOL.rename, ← bodyMeaning] using leftLambdaRead)
      (by simpa only [HOL.subst, HOL.rename, ← bodyMeaning] using rightLambdaRead)
    have lambdaConclusionRead : readFormulaIn abbreviation (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters)
        parameters names (entails signature.symbol antecedent (holds signature.symbol
          (equality signature.symbol (encodeType signature.symbol base (domain ⇒ bodyType))
            (encodeWithAssignment signature.symbol base constant binders
              (encodeSubstitution signature.symbol base constant binders assignment depth substitution) depth (Term.lam body))
            (encodeWithAssignment signature.symbol base constant binders assignment depth (HOL.subst substitution (Term.lam body)))))) =
        some (.imp g.formula (.eq (.lam (HOL.subst meaning body)) (.lam (HOL.subst meaning body)))) := by
      simp only [HOL.subst]
      rw [HOLKernelStructuralReadback.read_entails abbreviation signature.symbol_injective (distinct .im), lambdaEquationRead]
      simp only [readFormulaIn, contextRead, Option.map_some]
      rfl
    have rootFresh : HOLKernelBindingInterpretation.freshName parameters names (binders depth) = true := by
      simp [HOLKernelBindingInterpretation.freshName, headFresh, bindersAbove]
    let lambdaTree : AdmittedProof abbreviation theorems context (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters)
        parameters ruleAt bindingAt (max assignmentFuel recursiveFuel + 2) names abstractionEquality.val
        (.imp g.formula (.eq (.lam (HOL.subst meaning body)) (.lam (HOL.subst meaning body)))) :=
      AdmittedStep.binding abstractionEquality.property.eval {
        rule := .abstractionCongruence
        selected := bindingSelected .abstractionCongruence
        declared := binding.declared .abstractionCongruence
        conclusion_read := lambdaConclusionRead
        step := .abstractionCongruence rootFresh (by simpa only [nextG, Judgment.formula, Judgment.rename_formula, HOL.weaken] using bodyTree) }
    first
    | refine ⟨max assignmentFuel recursiveFuel + 2, ?_⟩
      simpa only [HOLKernelSubstitution.compile, HOL.subst, HOL.rename, bodyMeaning] using (⟨lambdaTree⟩ : Nonempty _)
    | first
      | refine ⟨max 1 (max assignmentFuel recursiveFuel + 2) + 2, ?_⟩
        simpa only [HOLKernelSubstitution.compile, HOL.subst, HOL.rename, bodyMeaning] using
          HOLKernelCongruenceReadback.universal_admitted signature abbreviation profile distinct dictionary parameters rules names antecedent
            (encodeType signature.symbol base domain) _ _ (binders depth) (binders depth) antecedentSorted domainSorted head head
            leftBodySorted rightBodySorted abstractionEquality g (HOL.subst meaning body) (HOL.subst meaning body)
            contextRead (typeRead domain) (bindersAbove depth) (bindersAbove depth) leftBodyRead
            (by rw [bodyMeaning]; exact rightBodyRead) ruleAt bindingAt (selected .applicationArgument) lambdaTree
      | refine ⟨max 1 (max assignmentFuel recursiveFuel + 2) + 2, ?_⟩
        simpa only [HOLKernelSubstitution.compile, HOL.subst, HOL.rename, bodyMeaning] using
          HOLKernelCongruenceReadback.existential_admitted signature abbreviation profile distinct dictionary parameters rules names antecedent
            (encodeType signature.symbol base domain) _ _ (binders depth) (binders depth) antecedentSorted domainSorted head head
            leftBodySorted rightBodySorted abstractionEquality g (HOL.subst meaning body) (HOL.subst meaning body)
            contextRead (typeRead domain) (bindersAbove depth) (bindersAbove depth) leftBodyRead
            (by rw [bodyMeaning]; exact rightBodyRead) ruleAt bindingAt (selected .applicationArgument) lambdaTree

#print axioms compile_admitted
/-- The actual single-variable comparison is admitted under its explicit
argument-equality assumption, with unchanged native receipt and theorem policy. -/
theorem instanceEquation_admitted (signature : Signature sorts terms)
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : HOLKernelTypingRules.Rules theorems signature.symbol signature.ids)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (base : Unit → Preterm) (constant : ∀ {type}, Const type → Preterm)
    (binders temporary : Nat → Nat)
    (baseSorted : ∀ index, Preterm.HasType terms context (base index) [] signature.ids.type)
    (constantSorted : ∀ {type} (symbol : Const type),
      Preterm.HasType terms context (constant symbol) [] signature.ids.object)
    (bindersInjective : Function.Injective binders) (temporaryInjective : Function.Injective temporary)
    (baseIndependent : ∀ slot index, ¬ Preterm.HasVar context (binders slot) (base index))
    (temporaryIndependent : ∀ slot index, ¬ Preterm.HasVar context (temporary slot) (base index))
    {gamma : Ctx Unit} {domain result : Ty Unit}
    (argument : Term Const gamma domain) (body : Term Const (domain :: gamma) result)
    (assignment : Assignment gamma) (depth temporaryDepth boundIndex : Nat)
    (antecedent argumentCode : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (argumentSorted : Preterm.HasType terms context argumentCode [] signature.ids.object)
    (bound : context[boundIndex]? = some (.bound signature.ids.object))
    (assignmentSorted : ∀ {type} (index : Var gamma type),
      Preterm.HasType terms context (assignment index) [] signature.ids.object)
    (slots : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument),
      context[binders (depth + offset)]? = some (.bound signature.ids.object))
    (temporarySlots : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument),
      context[temporary (temporaryDepth + offset)]? = some (.bound signature.ids.object))
    (fresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument),
      ¬ Preterm.HasVar context (binders (depth + offset))
        (conjunction signature.symbol antecedent
          (holds signature.symbol (equality signature.symbol (encodeType signature.symbol base domain)
            (.var boundIndex) argumentCode))))
    (temporaryFresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument),
      ¬ Preterm.HasVar context (temporary (temporaryDepth + offset))
        (conjunction signature.symbol antecedent
          (holds signature.symbol (equality signature.symbol (encodeType signature.symbol base domain)
            (.var boundIndex) argumentCode))))
    (disjoint : ∀ firstOffset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument),
      ∀ secondOffset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument),
        binders (depth + firstOffset) ≠ temporary (temporaryDepth + secondOffset))
    (variableTyping : ∀ {type} (index : Var gamma type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
        (context := context) (hypotheses := [])
        (typed signature.symbol antecedent (assignment index) (encodeType signature.symbol base type)))
    (constantTyping : ∀ {type} (symbol : Const type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
        (context := context) (hypotheses := [])
        (typed signature.symbol antecedent (constant symbol) (encodeType signature.symbol base type)))
    (argumentEquation : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := [])
      (entails signature.symbol antecedent (holds signature.symbol
        (equality signature.symbol (encodeType signature.symbol base domain) argumentCode
          (encodeWithAssignment signature.symbol base constant binders assignment depth argument)))))
    (distinct : ∀ symbol, signature.symbol symbol ≠ abbreviation.reference)
    (dictionary : Nat → Option (NamedElaboration.SomeConst Const))
    (indices : ∀ {type}, Const type → Nat) (parameters : Nat)
    (lookup : ∀ {type} (symbol : Const type), dictionary (indices symbol) = some ⟨type, symbol⟩)
    (bounded : ∀ {type} (symbol : Const type), indices symbol < parameters)
    (baseEq : base = fun _ => .var 0)
    (constantEq : ∀ {type} (symbol : Const type), constant symbol = .var (indices symbol))
    (bindersAbove : ∀ level, parameters ≤ binders level)
    (temporaryAbove : ∀ level, parameters ≤ temporary level)
    {target : Ctx Unit} (rho : Rename Unit gamma target) (names : Names target)
    (nodup : names.toList.Nodup) (namesAbove : ∀ name ∈ names.toList, parameters ≤ name)
    (assignmentEq : ∀ {type} (index : Var gamma type), assignment index = .var (names.nameOf (rho index)))
    (boundVar : Var target domain)
    (boundRead : names.lookup? boundIndex = some ⟨domain, boundVar⟩)
    (sourceNames : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument), binders (depth + offset) ∉ names.toList)
    (temporaryNames : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument), temporary (temporaryDepth + offset) ∉ names.toList)
    (dictionaryFresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument), dictionary (binders (depth + offset)) = none)
    (g : Judgment Const target)
    (contextRead : readJudgmentWith (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) signature.symbol names
      (expandEquivalence signature.symbol abbreviation.reference antecedent) = some g)
    (argumentRead : HOLKernelLogicalFunctionReadback.reader profile dictionary parameters names
      (expandEquivalence signature.symbol abbreviation.reference argumentCode) = some ⟨domain, HOL.rename rho argument⟩)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (selected : ∀ rule, ruleAt (rules.index rule) = some (.inference rule))
    (structuralSelected : ∀ rule, ruleAt (structural.index rule) = some (.structural rule))
    (bindingSelected : ∀ rule, bindingAt (binding.index rule) = some rule)
    (argumentAdmitted : AdmissionUnderRenaming (context := context) abbreviation profile dictionary parameters ruleAt bindingAt names
      argumentEquation.val (.imp g.formula (.eq (HOL.rename rho argument) (HOL.rename rho argument)))) :
    ∃ fuel, Nonempty (AdmittedProof abbreviation theorems context
      (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) parameters ruleAt bindingAt fuel names
      (HOLKernelSubstitution.instanceEquation signature profile structural typing rules binding base constant binders temporary
        baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent argument body assignment
        depth temporaryDepth boundIndex antecedent argumentCode antecedentSorted argumentSorted bound assignmentSorted slots temporarySlots
        fresh temporaryFresh disjoint variableTyping constantTyping argumentEquation).val
      (.imp (.and g.formula (.eq (.var boundVar) (HOL.rename rho argument)))
        (.eq (HOL.subst ((fun {type} (index : Var (domain :: gamma) type) => match index with | .vz => .var boundVar | .vs old => .var (rho old))) body)
          (HOL.rename rho (instantiate argument body))))) := by
  let extra := holds signature.symbol (equality signature.symbol (encodeType signature.symbol base domain)
    (.var boundIndex) argumentCode)
  let extended := conjunction signature.symbol antecedent extra
  have domainSorted := encodeType_sorted signature context base baseSorted domain
  have resultSorted := encodeType_sorted signature context base baseSorted result
  have variableSorted : Preterm.HasType terms context (.var boundIndex) [] signature.ids.object :=
    .var (binder := .bound signature.ids.object) bound
  have extraSorted := holds_sorted signature context (signature.application context .eqc _
    (.cons (.regular domainSorted) (.cons (.regular variableSorted) (.cons (.regular argumentSorted) .nil))))
  have extendedSorted := conjunction_sorted signature context antecedentSorted extraSorted
  have imageHeight : argument.binderDepth ≤ Subst.maxBinderDepth (Subst.single argument) :=
    Subst.binderDepth_le_maxBinderDepth (Subst.single argument) .vz
  have encodedArgumentSorted := encode_sorted signature context base constant binders baseSorted constantSorted
    argument assignment depth assignmentSorted (fun offset smaller => slots offset (by omega))
  let relation := HOLKernelStructuralRules.right (definitions := definitions) (hypotheses := [])
    signature structural antecedent extra antecedentSorted extraSorted
  let argumentEquationUnder := HOLKernelStructuralRules.weaken signature structural antecedent extra _
    antecedentSorted extraSorted (holds_sorted signature context (signature.application context .eqc _
      (.cons (.regular domainSorted) (.cons (.regular argumentSorted) (.cons (.regular encodedArgumentSorted) .nil)))))
    argumentEquation
  let relatedHead := HOLKernelInferenceProofs.Native.transitivity signature rules extended _ _ _ _
    extendedSorted domainSorted variableSorted argumentSorted encodedArgumentSorted relation argumentEquationUnder
  have leftSorted : ∀ {type} (index : Var (domain :: gamma) type),
      Preterm.HasType terms context (Assignment.extend (.var boundIndex) assignment index) [] signature.ids.object :=
    Assignment.extend_sorted signature context _ assignment variableSorted assignmentSorted
  have rightSorted : ∀ {type} (index : Var (domain :: gamma) type), Preterm.HasType terms context
      (encodeSubstitution signature.symbol base constant binders assignment depth (Subst.single argument) index)
      [] signature.ids.object :=
    encodeSubstitution_sorted signature context base constant binders baseSorted constantSorted
      (Subst.single argument) assignment depth assignmentSorted (fun offset smaller => slots offset (by omega))
  let related : ∀ {type} (index : Var (domain :: gamma) type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
        (context := context) (hypotheses := [])
        (entails signature.symbol extended (holds signature.symbol
          (equality signature.symbol (encodeType signature.symbol base type)
            (Assignment.extend (.var boundIndex) assignment index)
            (encodeSubstitution signature.symbol base constant binders assignment depth (Subst.single argument) index)))) := by
    intro type index
    cases index with
    | vz => exact relatedHead
    | vs index =>
        exact HOLKernelStructuralRules.weaken signature structural antecedent extra _ antecedentSorted extraSorted
          (holds_sorted signature context (signature.application context .eqc _
            (.cons (.regular (encodeType_sorted signature context base baseSorted type))
              (.cons (.regular (assignmentSorted index)) (.cons (.regular (assignmentSorted index)) .nil)))))
          (HOLKernelInferenceProofs.Native.reflexivity signature rules antecedent _ _ antecedentSorted
            (encodeType_sorted signature context base baseSorted type) (assignmentSorted index) (variableTyping index))
  let extendedVariables : ∀ {type} (index : Var gamma type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
        (context := context) (hypotheses := [])
        (typed signature.symbol extended (assignment index) (encodeType signature.symbol base type)) :=
    HOLKernelTermTyping.weakenVariables signature structural base assignment antecedent extra
      antecedentSorted extraSorted baseSorted assignmentSorted variableTyping
  let extendedConstants : ∀ {type} (symbol : Const type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
        (context := context) (hypotheses := [])
        (typed signature.symbol extended (constant symbol) (encodeType signature.symbol base type)) :=
    HOLKernelTermTyping.weakenConstants signature structural base constant antecedent extra
      antecedentSorted extraSorted baseSorted constantSorted constantTyping
  let compareAssignments := HOLKernelTermCongruence.congruence signature profile structural typing rules binding
    base constant binders baseSorted constantSorted bindersInjective baseIndependent body
    (Assignment.extend (.var boundIndex) assignment)
    (encodeSubstitution signature.symbol base constant binders assignment depth (Subst.single argument))
    depth extended extendedSorted leftSorted rightSorted (fun offset smaller => slots offset (by omega))
    (fun offset smaller => fresh offset (by omega)) related extendedConstants
  let compareSubstitution := HOLKernelSubstitution.compile signature profile structural typing rules binding base constant binders temporary
    baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent
    body (Subst.single argument) assignment depth temporaryDepth extended extendedSorted assignmentSorted
    slots temporarySlots fresh temporaryFresh disjoint extendedVariables extendedConstants
  have leftBodySorted := encode_sorted signature context base constant binders baseSorted constantSorted
    body _ depth leftSorted (fun offset smaller => slots offset (by omega))
  have bothSorted := substitution_encodings_sorted signature context base constant binders baseSorted constantSorted
    body (Subst.single argument) assignment depth assignmentSorted slots

  let leftMeaning : Subst Const (domain :: gamma) target := (fun {type} (index : Var (domain :: gamma) type) => match index with | .vz => .var boundVar | .vs old => .var (rho old))
  let rightMeaning : Subst Const (domain :: gamma) target := fun index => HOL.rename rho (Subst.single argument index)
  let extraMeaning : Judgment Const target := .assertion (.eq (.var boundVar) (HOL.rename rho argument))
  let extendedMeaning : Judgment Const target := .conjunction g extraMeaning
  have typeRead (type : Ty Unit) : readType signature.symbol
      (expandEquivalence signature.symbol abbreviation.reference (encodeType signature.symbol base type)) = some type := by
    rw [baseEq, expandEquivalence_encodeType_of_fixed signature.symbol abbreviation.reference distinct
      (fun _ : Unit => .var 0) (fun _ => by simp [expandEquivalence])]
    exact readType_encode signature.symbol signature.symbol_injective type
  have variableRead : HOLKernelLogicalFunctionReadback.reader profile dictionary parameters names
      (expandEquivalence signature.symbol abbreviation.reference (.var boundIndex)) = some ⟨domain, Term.var boundVar⟩ := by
    simp [expandEquivalence, HOLKernelLogicalFunctionReadback.reader, readTermWith, readVariable, boundRead]
  have encodedArgumentRead := HOLKernelAlphaReadback.encoded_read abbreviation profile distinct dictionary indices parameters lookup bounded
    base constant baseEq constantEq rho names assignment assignmentEq binders bindersInjective bindersAbove argument depth nodup namesAbove
    (by
      intro offset less type index
      exact BinderNames.ne_nameOf_of_not_mem names (sourceNames offset (by omega)) (rho index))
  have extraRead : readJudgmentWith (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) signature.symbol names
      (expandEquivalence signature.symbol abbreviation.reference extra) = some extraMeaning :=
    HOLKernelCongruenceReadback.equation_judgment_read signature abbreviation profile distinct dictionary parameters
      names _ _ _ (.var boundVar) (HOL.rename rho argument) (typeRead domain) variableRead argumentRead
  have extendedRead : readJudgmentWith (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) signature.symbol names
      (expandEquivalence signature.symbol abbreviation.reference extended) = some extendedMeaning := by
    simp [extended, conjunction, applySymbol, Preterm.applyArgs, expandEquivalence, distinct,
      readJudgmentWith, readHead_reference signature.symbol signature.symbol_injective, contextRead, extraRead, extendedMeaning]
  have argumentEquationRead := HOLKernelCongruenceReadback.equation_judgment_read signature abbreviation profile distinct dictionary parameters
    names _ _ _ (HOL.rename rho argument) (HOL.rename rho argument) (typeRead domain) argumentRead encodedArgumentRead
  have relatedHeadAdmitted : AdmissionUnderRenaming (context := context) abbreviation profile dictionary parameters ruleAt bindingAt names
      relatedHead.val (.imp extendedMeaning.formula (.eq (.var boundVar) (HOL.rename rho argument))) := by
    have relationAdmitted : AdmissionUnderRenaming (context := context) abbreviation profile dictionary parameters ruleAt bindingAt names
        relation.val (.imp extendedMeaning.formula extraMeaning.formula) :=
      HOLKernelStructuralReadback.right_admission_under_renaming signature abbreviation profile distinct dictionary parameters
        structural names antecedent extra antecedentSorted extraSorted g extraMeaning contextRead extraRead ruleAt bindingAt (structuralSelected .anr)
    have underAdmitted : AdmissionUnderRenaming (context := context) abbreviation profile dictionary parameters ruleAt bindingAt names
        argumentEquationUnder.val (.imp extendedMeaning.formula (.eq (HOL.rename rho argument) (HOL.rename rho argument))) :=
      HOLKernelStructuralReadback.weaken_admission_under_renaming signature abbreviation profile distinct dictionary parameters
        structural names antecedent extra _ antecedentSorted extraSorted _ argumentEquation g extraMeaning
        (.assertion (.eq (HOL.rename rho argument) (HOL.rename rho argument))) contextRead extraRead argumentEquationRead
        ruleAt bindingAt structuralSelected argumentAdmitted
    intro futureContext rhoNext future futureNodup futureAbove futureLookup
    exact HOLKernelCongruenceReadback.transitivity_admission_under_renaming signature abbreviation profile distinct dictionary parameters
      rules names extended _ _ _ _ extendedSorted domainSorted variableSorted argumentSorted encodedArgumentSorted relation argumentEquationUnder
      extendedMeaning (.var boundVar) (HOL.rename rho argument) (HOL.rename rho argument) extendedRead (typeRead domain)
      variableRead argumentRead encodedArgumentRead ruleAt bindingAt (selected .transitivity) relationAdmitted underAdmitted rhoNext future futureNodup futureAbove futureLookup
  have oldRead {type : Ty Unit} (index : Var gamma type) : HOLKernelLogicalFunctionReadback.reader profile dictionary parameters names
      (expandEquivalence signature.symbol abbreviation.reference (assignment index)) = some ⟨type, Term.var (rho index)⟩ := by
    simp [assignmentEq, expandEquivalence, HOLKernelLogicalFunctionReadback.reader, readTermWith, readVariable,
      BinderNames.lookup?_nameOf names nodup]
  have relatedAdmitted : ∀ {type} (index : Var (domain :: gamma) type),
      AdmissionUnderRenaming (context := context) abbreviation profile dictionary parameters ruleAt bindingAt names
        (related index).val (.imp extendedMeaning.formula (.eq (leftMeaning index) (rightMeaning index))) := by
    intro type index
    cases index with
    | vz =>
      intro futureContext rhoNext future futureNodup futureAbove futureLookup
      exact relatedHeadAdmitted rhoNext future futureNodup futureAbove futureLookup
    | vs index =>
      let reflProof := HOLKernelInferenceProofs.Native.reflexivity (definitions := definitions) (hypotheses := []) signature rules antecedent _ _ antecedentSorted
        (encodeType_sorted signature context base baseSorted type) (assignmentSorted index) (variableTyping index)
      have reflAdmitted : AdmissionUnderRenaming (context := context) abbreviation profile dictionary parameters ruleAt bindingAt names
          reflProof.val (.imp g.formula (.eq (.var (rho index)) (.var (rho index)))) :=
        HOLKernelCongruenceReadback.reflexivity_admission_under_renaming signature abbreviation profile distinct dictionary parameters
          rules names antecedent _ _ antecedentSorted _ _ (variableTyping index) g (.var (rho index))
          contextRead (typeRead type) (oldRead index) ruleAt bindingAt (selected .reflexivity)
      have equalityRead := HOLKernelCongruenceReadback.equation_judgment_read signature abbreviation profile distinct dictionary parameters
        names _ _ _ (.var (rho index)) (.var (rho index)) (typeRead type) (oldRead index) (oldRead index)
      intro futureContext rhoNext future futureNodup futureAbove futureLookup
      exact HOLKernelStructuralReadback.weaken_admission_under_renaming signature abbreviation profile distinct dictionary parameters
        structural names antecedent extra _ antecedentSorted extraSorted _ reflProof g extraMeaning (.assertion (.eq (.var (rho index)) (.var (rho index))))
        contextRead extraRead equalityRead ruleAt bindingAt structuralSelected reflAdmitted rhoNext future futureNodup futureAbove futureLookup
  have leftReads : ∀ {type} (index : Var (domain :: gamma) type),
      HOLKernelLogicalFunctionReadback.reader profile dictionary parameters names
        (Assignment.extend (.var boundIndex) assignment index) = some ⟨type, leftMeaning index⟩ := by
    intro type index
    cases index with
    | vz => simpa only [leftMeaning, Assignment.extend, expandEquivalence] using variableRead
    | vs index => simpa only [leftMeaning, Assignment.extend, assignmentEq, expandEquivalence] using oldRead index
  have rightFixed : ∀ {type} (index : Var (domain :: gamma) type),
      expandEquivalence signature.symbol abbreviation.reference
        (encodeSubstitution signature.symbol base constant binders assignment depth (Subst.single argument) index) =
      encodeSubstitution signature.symbol base constant binders assignment depth (Subst.single argument) index := by
    intro type index
    apply expandEquivalence_encodeWithAssignment_of_fixed signature.symbol abbreviation.reference distinct
    · intro name; simp [baseEq, expandEquivalence]
    · intro type symbol; simp [constantEq, expandEquivalence]
    · intro type index; simp [assignmentEq, expandEquivalence]
  have rightReads : ∀ {type} (index : Var (domain :: gamma) type),
      HOLKernelLogicalFunctionReadback.reader profile dictionary parameters names
        (encodeSubstitution signature.symbol base constant binders assignment depth (Subst.single argument) index) = some ⟨type, rightMeaning index⟩ := by
    intro type index
    cases index with
    | vz =>
      have fixed := rightFixed (Var.vz : Var (domain :: gamma) domain)
      simp only [encodeSubstitution, Subst.single] at fixed
      rw [fixed] at encodedArgumentRead
      exact encodedArgumentRead
    | vs index => simpa only [rightMeaning, Subst.single, HOL.rename, encodeSubstitution, encodeWithAssignment, assignmentEq, expandEquivalence] using oldRead index
  have leftFixed : ∀ {type} (index : Var (domain :: gamma) type),
      expandEquivalence signature.symbol abbreviation.reference (Assignment.extend (.var boundIndex) assignment index) =
      Assignment.extend (.var boundIndex) assignment index := by
    intro type index
    cases index <;> simp [Assignment.extend, assignmentEq, expandEquivalence]
  have constantsAbsent : ∀ {type} (symbol : Const type), names.lookup? (indices symbol) = none := by
    intro type symbol
    apply BinderNames.lookup?_none_of_not_mem
    intro member
    have h := namesAbove _ member
    have h' := bounded symbol
    omega
  have freshLookup := fun offset less => BinderNames.lookup?_none_of_not_mem names (sourceNames offset less)
  obtain ⟨comparisonFuel, ⟨comparisonTree⟩⟩ := HOLKernelTermCongruenceReadback.congruence_admitted signature abbreviation profile structural typing rules binding
    distinct dictionary indices parameters lookup bounded base constant baseEq constantEq binders baseSorted constantSorted bindersInjective bindersAbove baseIndependent body
    (Assignment.extend (.var boundIndex) assignment) (encodeSubstitution signature.symbol base constant binders assignment depth (Subst.single argument))
    depth extended extendedSorted leftSorted rightSorted (fun offset less => slots offset (by omega)) (fun offset less => fresh offset (by omega)) related extendedConstants
    leftMeaning rightMeaning names nodup namesAbove leftReads rightReads leftFixed rightFixed constantsAbsent
    (fun offset less => freshLookup offset (by omega)) (fun offset less => dictionaryFresh offset (by omega))
    extendedMeaning extendedRead ruleAt bindingAt selected structuralSelected (bindingSelected .abstractionCongruence) relatedAdmitted
  obtain ⟨substitutionFuel, ⟨substitutionTree⟩⟩ := compile_admitted signature abbreviation profile structural typing rules binding
    distinct dictionary indices parameters lookup bounded base constant baseEq constantEq binders temporary baseSorted constantSorted bindersInjective temporaryInjective
    bindersAbove temporaryAbove baseIndependent temporaryIndependent body (Subst.single argument) assignment depth temporaryDepth extended extendedSorted assignmentSorted
    slots temporarySlots fresh temporaryFresh disjoint extendedVariables extendedConstants rho names nodup namesAbove assignmentEq sourceNames temporaryNames dictionaryFresh
    extendedMeaning extendedRead ruleAt bindingAt selected structuralSelected bindingSelected
  have leftRead := HOLKernelTermCongruenceReadback.assigned_read signature abbreviation profile distinct dictionary indices parameters lookup bounded
    base constant baseEq constantEq binders bindersInjective bindersAbove body leftMeaning (Assignment.extend (.var boundIndex) assignment) names depth
    leftReads leftFixed constantsAbsent (fun offset less => freshLookup offset (by omega)) (fun offset less => dictionaryFresh offset (by omega))
  have bothReads := substitution_read signature abbreviation profile distinct dictionary indices parameters lookup bounded base constant baseEq constantEq
    binders bindersInjective bindersAbove body (Subst.single argument) assignment depth rho names nodup namesAbove assignmentEq sourceNames dictionaryFresh
  have rightSame : HOL.subst rightMeaning body = HOL.rename rho (instantiate argument body) :=
    (rename_subst rho (Subst.single argument) body).symm
  have witnessEq :
      (HOLKernelSubstitution.instanceEquation signature profile structural typing rules binding base constant binders temporary
        baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent argument body assignment
        depth temporaryDepth boundIndex antecedent argumentCode antecedentSorted argumentSorted bound assignmentSorted slots temporarySlots
        fresh temporaryFresh disjoint variableTyping constantTyping argumentEquation).val =
      (HOLKernelInferenceProofs.Native.transitivity signature rules extended _ _ _ _ extendedSorted resultSorted
        leftBodySorted bothSorted.1 bothSorted.2 compareAssignments compareSubstitution).val := rfl
  rw [witnessEq]
  refine ⟨max comparisonFuel substitutionFuel + 1, ?_⟩
  exact HOLKernelCongruenceReadback.transitivity_admitted signature abbreviation profile distinct dictionary parameters
    rules names extended _ _ _ _ extendedSorted resultSorted leftBodySorted bothSorted.1 bothSorted.2 compareAssignments compareSubstitution
    extendedMeaning (HOL.subst leftMeaning body) (HOL.rename rho (instantiate argument body)) (HOL.rename rho (instantiate argument body))
    extendedRead (typeRead result) leftRead bothReads.1 bothReads.2 ruleAt bindingAt (selected .transitivity)
    (by simpa only [rightSame] using comparisonTree) substitutionTree

#print axioms instanceEquation_admitted

end Mettapedia.Languages.MM0.HOLKernelSubstitutionReadback
