import Mettapedia.Languages.MM0.HOLKernelSubstitutionReadback
import Mettapedia.Languages.MM0.HOLKernelSourceInstantiation
import Mettapedia.Languages.MM0.HOLKernelQuantifierReadback

/-!
# Admission of source-derived instantiation and beta receipts

The actual single-variable instance comparison is reconstructed in its extended
source frame, keeping the argument-equality assumption and fresh native binder.
The derived instance equation is shared by beta and quantifier instantiation.
The source beta construction then admits the actual native beta application and
recovers the exact renamed source redex and substituted result.

The argument-equation receipt must retain admission under successful frame
transport. Native sorting, occurrence independence, both finite name banks,
constant lookup and theorem selection remain explicit. Canonical beta joins
argument rebinding, the native beta application and result rebinding back to
the original encoding. Universal elimination and existential
introduction reuse the shared instance equation through the maintained
Boolean-equivalence definition and retain their actual premise receipts.
Their canonical forms promote the prepared receipts through the retained
logical-to-formation projection, whose native scope bound protects the new
binder frame, and return to the original source encoding.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.MM0.HOLKernelSourceInstantiationReadback
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
theorem deriveInstance_equation_admitted (signature : Signature sorts terms)
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
    (assignment : Assignment gamma) (depth temporaryDepth : Nat)
    (antecedent argumentCode : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (argumentSorted : Preterm.HasType terms context argumentCode [] signature.ids.object)
    (assignmentSorted : ∀ {type} (index : Var gamma type),
      Preterm.HasType terms context (assignment index) [] signature.ids.object)
    (slots : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      context[binders (depth + offset)]? = some (.bound signature.ids.object))
    (temporarySlots : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument),
      context[temporary (temporaryDepth + offset)]? = some (.bound signature.ids.object))
    (fresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      ¬ Preterm.HasVar context (binders (depth + offset)) antecedent)
    (equationFresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument),
      ¬ Preterm.HasVar context (binders (depth + 1 + offset))
        (conjunction signature.symbol antecedent
          (holds signature.symbol (equality signature.symbol (encodeType signature.symbol base domain)
            (.var (binders depth)) argumentCode))))
    (temporaryFresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument),
      ¬ Preterm.HasVar context (temporary (temporaryDepth + offset))
        (conjunction signature.symbol antecedent
          (holds signature.symbol (equality signature.symbol (encodeType signature.symbol base domain)
            (.var (binders depth)) argumentCode))))
    (disjoint : ∀ firstOffset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument),
      ∀ secondOffset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument),
        binders (depth + 1 + firstOffset) ≠ temporary (temporaryDepth + secondOffset))
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
          (encodeWithAssignment signature.symbol base constant binders assignment (depth + 1) argument)))))
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
    (sourceNames : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1, binders (depth + offset) ∉ names.toList)
    (temporaryNames : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument), temporary (temporaryDepth + offset) ∉ names.toList)
    (dictionaryFresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1, dictionary (binders (depth + offset)) = none)
    (temporaryApartHead : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument), temporary (temporaryDepth + offset) ≠ binders depth)
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
      (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) parameters ruleAt bindingAt fuel
      (BinderNames.cons (type := domain) (binders depth) names)
      (HOLKernelSourceInstantiation.deriveInstance signature profile structural typing rules binding base constant binders temporary
        baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent argument body
        assignment depth temporaryDepth antecedent argumentCode antecedentSorted argumentSorted assignmentSorted
        slots temporarySlots fresh equationFresh temporaryFresh disjoint variableTyping constantTyping argumentEquation).equation.val
      (.imp (.and (weaken (σ := domain) g.formula) (.eq (.var .vz) (weaken (σ := domain) (HOL.rename rho argument))))
        (.eq (HOL.rename (Rename.lift rho) body) (weaken (σ := domain) (HOL.rename rho (instantiate argument body)))))) := by
  let derived := HOLKernelSourceInstantiation.deriveInstance signature profile structural typing rules binding base constant binders temporary
    baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent argument body
    assignment depth temporaryDepth antecedent argumentCode antecedentSorted argumentSorted assignmentSorted
    slots temporarySlots fresh equationFresh temporaryFresh disjoint variableTyping constantTyping argumentEquation
  have head : context[binders depth]? = some (.bound signature.ids.object) := by
    simpa only [Nat.add_zero] using slots 0 (by omega)
  have bodySlots : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument),
      context[binders (depth + 1 + offset)]? = some (.bound signature.ids.object) := by
    intro offset less
    have found := slots (offset + 1) (by omega)
    simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using found
  let nextNames : Names (domain :: target) := BinderNames.cons (binders depth) names
  let shiftedRho : Rename Unit gamma (domain :: target) := fun index => Var.vs (rho index)
  have headAbsent : binders depth ∉ names.toList := by
    simpa only [Nat.add_zero] using sourceNames 0 (by omega)
  have headLookup : names.lookup? (binders depth) = none := BinderNames.lookup?_none_of_not_mem names headAbsent
  have headDictionary : dictionary (binders depth) = none := by
    simpa only [Nat.add_zero] using dictionaryFresh 0 (by omega)
  have nextLookup : LookupPreserving dictionary (Rename.weaken (σ := domain)) names nextNames :=
    LookupPreserving.weaken dictionary names domain (binders depth) headLookup headDictionary
  have nextNodup : nextNames.toList.Nodup := List.nodup_cons.mpr ⟨headAbsent, nodup⟩
  have nextAbove : ∀ name ∈ nextNames.toList, parameters ≤ name := by
    intro name member
    rcases List.mem_cons.mp member with rfl | member
    · exact bindersAbove depth
    · exact namesAbove _ member
  have nextAssignment : ∀ {type} (index : Var gamma type), assignment index = .var (nextNames.nameOf (shiftedRho index)) := assignmentEq
  have sourceNext : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument), binders (depth + 1 + offset) ∉ nextNames.toList := by
    intro offset less member
    rcases List.mem_cons.mp member with same | old
    · have impossible := bindersInjective same
      omega
    · have absent := sourceNames (offset + 1) (by omega)
      apply absent
      simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using old
  have temporaryNext : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument), temporary (temporaryDepth + offset) ∉ nextNames.toList := by
    intro offset less member
    rcases List.mem_cons.mp member with same | old
    · exact temporaryApartHead offset less same
    · exact temporaryNames offset less old
  have dictionaryNext : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument), dictionary (binders (depth + 1 + offset)) = none := by
    intro offset less
    have found := dictionaryFresh (offset + 1) (by omega)
    simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using found
  have nextContextRead := logical_judgment_rename_of_read profile dictionary parameters names nextNames
    (Rename.weaken (σ := domain)) nextLookup _ g contextRead
  have nextArgumentRead : HOLKernelLogicalFunctionReadback.reader profile dictionary parameters nextNames
      (expandEquivalence signature.symbol abbreviation.reference argumentCode) = some ⟨domain, HOL.rename shiftedRho argument⟩ := by
    have found := logical_reader_rename_of_read profile dictionary parameters names nextNames
      (Rename.weaken (σ := domain)) nextLookup _ (HOL.rename rho argument) argumentRead
    simpa only [rename_comp, Rename.weaken, shiftedRho] using found
  have nextArgumentAdmitted : AdmissionUnderRenaming (context := context) abbreviation profile dictionary parameters ruleAt bindingAt nextNames
      argumentEquation.val (.imp (g.rename (Rename.weaken (σ := domain))).formula
        (.eq (HOL.rename shiftedRho argument) (HOL.rename shiftedRho argument))) := by
    intro futureContext rhoNext future futureNodup futureAbove futureLookup
    have found := argumentAdmitted (fun index => rhoNext (Var.vs index)) future futureNodup futureAbove (nextLookup.comp futureLookup)
    simpa only [HOL.rename, Judgment.rename_formula, rename_comp, shiftedRho, Rename.weaken] using found
  obtain ⟨equationFuel, ⟨equationTree⟩⟩ := HOLKernelSubstitutionReadback.instanceEquation_admitted signature abbreviation profile structural typing rules binding
    base constant binders temporary baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent
    argument body assignment (depth + 1) temporaryDepth (binders depth) antecedent argumentCode antecedentSorted argumentSorted head assignmentSorted
    bodySlots temporarySlots equationFresh temporaryFresh disjoint variableTyping constantTyping argumentEquation distinct dictionary indices parameters lookup bounded
    baseEq constantEq bindersAbove temporaryAbove shiftedRho nextNames nextNodup nextAbove nextAssignment .vz
    (by simp [nextNames]) sourceNext temporaryNext dictionaryNext (g.rename (Rename.weaken (σ := domain))) nextContextRead nextArgumentRead
    ruleAt bindingAt selected structuralSelected bindingSelected nextArgumentAdmitted
  have derivedWitness : derived.equation.val =
      (HOLKernelSubstitution.instanceEquation signature profile structural typing rules binding base constant binders temporary
        baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent argument body assignment
        (depth + 1) temporaryDepth (binders depth) antecedent argumentCode antecedentSorted argumentSorted head assignmentSorted
        bodySlots temporarySlots equationFresh temporaryFresh disjoint variableTyping constantTyping argumentEquation).val := rfl
  have equationTree' : AdmittedProof abbreviation theorems context
      (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) parameters ruleAt bindingAt equationFuel nextNames
      derived.equation.val
      (.imp (.and (g.rename (Rename.weaken (σ := domain))).formula (.eq (.var .vz) (HOL.rename shiftedRho argument)))
        (.eq (HOL.rename (Rename.lift rho) body) (HOL.rename shiftedRho (instantiate argument body)))) := by
    rw [derivedWitness]
    convert equationTree using 1
    congr 2
    rw [← subst_ofRename (Rename.lift rho) body]
    exact subst_ext (by intro type index; cases index <;> rfl) body
  refine ⟨equationFuel, ⟨?_⟩⟩
  simpa only [Judgment.rename_formula, weaken, rename_comp, shiftedRho, Rename.weaken] using equationTree'

#print axioms deriveInstance_equation_admitted

theorem beta_admitted (signature : Signature sorts terms)
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
    (assignment : Assignment gamma) (depth temporaryDepth : Nat)
    (antecedent argumentCode : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (argumentSorted : Preterm.HasType terms context argumentCode [] signature.ids.object)
    (assignmentSorted : ∀ {type} (index : Var gamma type),
      Preterm.HasType terms context (assignment index) [] signature.ids.object)
    (slots : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      context[binders (depth + offset)]? = some (.bound signature.ids.object))
    (temporarySlots : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument),
      context[temporary (temporaryDepth + offset)]? = some (.bound signature.ids.object))
    (fresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      ¬ Preterm.HasVar context (binders (depth + offset)) antecedent)
    (equationFresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument),
      ¬ Preterm.HasVar context (binders (depth + 1 + offset))
        (conjunction signature.symbol antecedent
          (holds signature.symbol (equality signature.symbol (encodeType signature.symbol base domain)
            (.var (binders depth)) argumentCode))))
    (temporaryFresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument),
      ¬ Preterm.HasVar context (temporary (temporaryDepth + offset))
        (conjunction signature.symbol antecedent
          (holds signature.symbol (equality signature.symbol (encodeType signature.symbol base domain)
            (.var (binders depth)) argumentCode))))
    (disjoint : ∀ firstOffset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument),
      ∀ secondOffset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument),
        binders (depth + 1 + firstOffset) ≠ temporary (temporaryDepth + secondOffset))
    (variableTyping : ∀ {type} (index : Var gamma type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
        (context := context) (hypotheses := [])
        (typed signature.symbol antecedent (assignment index) (encodeType signature.symbol base type)))
    (constantTyping : ∀ {type} (symbol : Const type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
        (context := context) (hypotheses := [])
        (typed signature.symbol antecedent (constant symbol) (encodeType signature.symbol base type)))
    (argumentTyping : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := [])
      (typed signature.symbol antecedent argumentCode (encodeType signature.symbol base domain)))
    (argumentEquation : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := [])
      (entails signature.symbol antecedent (holds signature.symbol
        (equality signature.symbol (encodeType signature.symbol base domain) argumentCode
          (encodeWithAssignment signature.symbol base constant binders assignment (depth + 1) argument)))))
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
    (sourceNames : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1, binders (depth + offset) ∉ names.toList)
    (temporaryNames : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument), temporary (temporaryDepth + offset) ∉ names.toList)
    (dictionaryFresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1, dictionary (binders (depth + offset)) = none)
    (temporaryApartHead : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument), temporary (temporaryDepth + offset) ≠ binders depth)
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
      (HOLKernelSourceInstantiation.beta signature profile structural typing rules binding base constant binders temporary
        baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent argument body assignment
        depth temporaryDepth antecedent argumentCode antecedentSorted argumentSorted assignmentSorted slots temporarySlots
        fresh equationFresh temporaryFresh disjoint variableTyping constantTyping argumentTyping argumentEquation).val
      (.imp g.formula (.eq (.app (.lam (HOL.rename (Rename.lift rho) body)) (HOL.rename rho argument))
        (HOL.rename rho (instantiate argument body))))) := by
  let compiled := HOLKernelSourceInstantiation.beta signature profile structural typing rules binding base constant binders temporary
    baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent argument body assignment
    depth temporaryDepth antecedent argumentCode antecedentSorted argumentSorted assignmentSorted slots temporarySlots
    fresh equationFresh temporaryFresh disjoint variableTyping constantTyping argumentTyping argumentEquation
  let derived := HOLKernelSourceInstantiation.deriveInstance signature profile structural typing rules binding base constant binders temporary
        baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent argument body
        assignment depth temporaryDepth antecedent argumentCode antecedentSorted argumentSorted assignmentSorted
        slots temporarySlots fresh equationFresh temporaryFresh disjoint variableTyping constantTyping argumentEquation
  obtain ⟨equationFuel, ⟨equationTree⟩⟩ := deriveInstance_equation_admitted signature abbreviation profile structural typing rules binding
    base constant binders temporary baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent
    argument body assignment depth temporaryDepth antecedent argumentCode antecedentSorted argumentSorted assignmentSorted
    slots temporarySlots fresh equationFresh temporaryFresh disjoint variableTyping constantTyping argumentEquation
    distinct dictionary indices parameters lookup bounded baseEq constantEq bindersAbove temporaryAbove rho names nodup namesAbove assignmentEq
    sourceNames temporaryNames dictionaryFresh temporaryApartHead g contextRead argumentRead ruleAt bindingAt selected structuralSelected bindingSelected argumentAdmitted
  have headAbsent : binders depth ∉ names.toList := by
    simpa only [Nat.add_zero] using sourceNames 0 (by omega)
  have headLookup : names.lookup? (binders depth) = none := BinderNames.lookup?_none_of_not_mem names headAbsent
  have typeRead (type : Ty Unit) : readType signature.symbol
      (expandEquivalence signature.symbol abbreviation.reference (encodeType signature.symbol base type)) = some type := by
    rw [baseEq, expandEquivalence_encodeType_of_fixed signature.symbol abbreviation.reference distinct
      (fun _ : Unit => .var 0) (fun _ => by simp [expandEquivalence])]
    exact readType_encode signature.symbol signature.symbol_injective type
  have functionRead := HOLKernelAlphaReadback.encoded_read abbreviation profile distinct dictionary indices parameters lookup bounded
    base constant baseEq constantEq rho names assignment assignmentEq binders bindersInjective bindersAbove (.lam body) depth nodup namesAbove
    (by
      intro offset less type index
      exact BinderNames.ne_nameOf_of_not_mem names (sourceNames offset (by simp only [Term.binderDepth] at less; omega)) (rho index))
  have resultRead := HOLKernelAlphaReadback.encoded_read abbreviation profile distinct dictionary indices parameters lookup bounded
    base constant baseEq constantEq rho names assignment assignmentEq binders bindersInjective bindersAbove (instantiate argument body) (depth + 1) nodup namesAbove
    (by
      intro offset less type index
      have height := Term.binderDepth_subst_le body (Subst.single argument)
      have absent := sourceNames (offset + 1) (by change offset < (HOL.subst (Subst.single argument) body).binderDepth at less; omega)
      apply BinderNames.ne_nameOf_of_not_mem names _ (rho index)
      simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using absent)
  have appRead : HOLKernelLogicalFunctionReadback.reader profile dictionary parameters names
      (expandEquivalence signature.symbol abbreviation.reference
        (applySymbol signature.symbol .app [encodeWithAssignment signature.symbol base constant binders assignment depth (.lam body), argumentCode])) =
      some ⟨result, Term.app (.lam (HOL.rename (Rename.lift rho) body)) (HOL.rename rho argument)⟩ := by
    simp only [applySymbol, Preterm.applyArgs, expandEquivalence, if_neg (distinct .app)]
    exact readTermWith_application (HOLKernelLogicalFunctionReadback.atoms profile) signature.symbol signature.symbol_injective dictionary parameters
      names _ _ (.lam (HOL.rename (Rename.lift rho) body)) (HOL.rename rho argument) functionRead argumentRead
  have equalityRead := HOLKernelCongruenceReadback.equation_read signature abbreviation profile distinct dictionary parameters
    names (encodeType signature.symbol base result) _ _ (.app (.lam (HOL.rename (Rename.lift rho) body)) (HOL.rename rho argument))
    (HOL.rename rho (instantiate argument body)) (typeRead result) appRead resultRead
  have conclusionRead : readFormulaIn abbreviation (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) parameters names
      (entails signature.symbol antecedent (holds signature.symbol
        (equality signature.symbol (encodeType signature.symbol base result)
          (applySymbol signature.symbol .app [encodeWithAssignment signature.symbol base constant binders assignment depth (.lam body), argumentCode])
          (encodeWithAssignment signature.symbol base constant binders assignment (depth + 1) (instantiate argument body))))) =
      some (.imp g.formula (.eq (.app (.lam (HOL.rename (Rename.lift rho) body)) (HOL.rename rho argument)) (HOL.rename rho (instantiate argument body)))) := by
    rw [HOLKernelStructuralReadback.read_entails abbreviation signature.symbol_injective (distinct .im), equalityRead]
    simp only [readFormulaIn, contextRead, Option.map_some]
    rfl
  have freshName : HOLKernelBindingInterpretation.freshName parameters names (binders depth) = true := by
    simp [HOLKernelBindingInterpretation.freshName, bindersAbove, headLookup]
  refine ⟨equationFuel + 1, ?_⟩
  exact ⟨AdmittedStep.binding compiled.property.eval {
    rule := .beta
    selected := bindingSelected .beta
    declared := binding.declared .beta
    conclusion_read := conclusionRead
    step := .beta freshName equationTree (by
      simp only [HOL.subst, Subst.single]
      have singleWeak {type : Ty Unit} (term : Term Const target type) :
          HOL.subst (Subst.single (HOL.rename rho argument)) (weaken (σ := domain) term) = term := instantiate_weaken _ _
      simp only [singleWeak]
      rfl) }⟩

#print axioms beta_admitted
/-- The source SPEC construction retains its substitution receipt and definition conversion. -/
theorem universalElimination_admitted (signature : Signature sorts terms)
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
    {gamma : Ctx Unit} {domain : Ty Unit}
    (argument : Term Const gamma domain) (body : Term Const (domain :: gamma) .prop)
    (assignment : Assignment gamma) (depth temporaryDepth : Nat)
    (antecedent argumentCode : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (argumentSorted : Preterm.HasType terms context argumentCode [] signature.ids.object)
    (assignmentSorted : ∀ {type} (index : Var gamma type),
      Preterm.HasType terms context (assignment index) [] signature.ids.object)
    (slots : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      context[binders (depth + offset)]? = some (.bound signature.ids.object))
    (temporarySlots : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument),
      context[temporary (temporaryDepth + offset)]? = some (.bound signature.ids.object))
    (fresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      ¬ Preterm.HasVar context (binders (depth + offset)) antecedent)
    (equationFresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument),
      ¬ Preterm.HasVar context (binders (depth + 1 + offset))
        (conjunction signature.symbol antecedent
          (holds signature.symbol (equality signature.symbol (encodeType signature.symbol base domain)
            (.var (binders depth)) argumentCode))))
    (temporaryFresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument),
      ¬ Preterm.HasVar context (temporary (temporaryDepth + offset))
        (conjunction signature.symbol antecedent
          (holds signature.symbol (equality signature.symbol (encodeType signature.symbol base domain)
            (.var (binders depth)) argumentCode))))
    (disjoint : ∀ firstOffset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument),
      ∀ secondOffset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument),
        binders (depth + 1 + firstOffset) ≠ temporary (temporaryDepth + secondOffset))
    (variableTyping : ∀ {type} (index : Var gamma type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
        (context := context) (hypotheses := [])
        (typed signature.symbol antecedent (assignment index) (encodeType signature.symbol base type)))
    (constantTyping : ∀ {type} (symbol : Const type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
        (context := context) (hypotheses := [])
        (typed signature.symbol antecedent (constant symbol) (encodeType signature.symbol base type)))
    (argumentTyping : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := [])
      (typed signature.symbol antecedent argumentCode (encodeType signature.symbol base domain)))
    (argumentEquation : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := [])
      (entails signature.symbol antecedent (holds signature.symbol
        (equality signature.symbol (encodeType signature.symbol base domain) argumentCode
          (encodeWithAssignment signature.symbol base constant binders assignment (depth + 1) argument)))))
    (universal : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := [])
      (entails signature.symbol antecedent (holds signature.symbol
        (encodeWithAssignment signature.symbol base constant binders assignment depth (.all body)))))
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
    (sourceNames : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1, binders (depth + offset) ∉ names.toList)
    (temporaryNames : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument), temporary (temporaryDepth + offset) ∉ names.toList)
    (dictionaryFresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1, dictionary (binders (depth + offset)) = none)
    (temporaryApartHead : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument), temporary (temporaryDepth + offset) ≠ binders depth)
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
      argumentEquation.val (.imp g.formula (.eq (HOL.rename rho argument) (HOL.rename rho argument))))
    {universalFuel : Nat}
    (universalAdmitted : AdmittedProof abbreviation theorems context
      (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) parameters ruleAt bindingAt universalFuel names universal.val
      (.imp g.formula (.all (HOL.rename (Rename.lift rho) body)))) :
    ∃ fuel, Nonempty (AdmittedProof abbreviation theorems context
      (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) parameters ruleAt bindingAt fuel names
      (HOLKernelSourceInstantiation.universalElimination signature abbreviation profile structural typing rules binding base constant binders temporary
        baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent argument body assignment
        depth temporaryDepth antecedent argumentCode antecedentSorted argumentSorted assignmentSorted slots temporarySlots
        fresh equationFresh temporaryFresh disjoint variableTyping constantTyping argumentTyping argumentEquation universal).val
      (.imp g.formula (HOL.rename rho (instantiate argument body)))) := by
  let derived := HOLKernelSourceInstantiation.deriveInstance signature profile structural typing rules binding base constant binders temporary
    baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent argument body
    assignment depth temporaryDepth antecedent argumentCode antecedentSorted argumentSorted assignmentSorted
    slots temporarySlots fresh equationFresh temporaryFresh disjoint variableTyping constantTyping argumentEquation
  obtain ⟨equationFuel, ⟨equationTree⟩⟩ := deriveInstance_equation_admitted signature abbreviation profile structural typing rules binding
    base constant binders temporary baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent
    argument body assignment depth temporaryDepth antecedent argumentCode antecedentSorted argumentSorted assignmentSorted
    slots temporarySlots fresh equationFresh temporaryFresh disjoint variableTyping constantTyping argumentEquation
    distinct dictionary indices parameters lookup bounded baseEq constantEq bindersAbove temporaryAbove rho names nodup namesAbove assignmentEq
    sourceNames temporaryNames dictionaryFresh temporaryApartHead g contextRead argumentRead ruleAt bindingAt selected structuralSelected bindingSelected argumentAdmitted
  have head : context[binders depth]? = some (.bound signature.ids.object) := by
    simpa only [Nat.add_zero] using slots 0 (by omega)
  have headAbsent : binders depth ∉ names.toList := by
    simpa only [Nat.add_zero] using sourceNames 0 (by omega)
  have headLookup : names.lookup? (binders depth) = none := BinderNames.lookup?_none_of_not_mem names headAbsent
  have headDictionary : dictionary (binders depth) = none := by
    simpa only [Nat.add_zero] using dictionaryFresh 0 (by omega)
  have typeRead (type : Ty Unit) : readType signature.symbol
      (expandEquivalence signature.symbol abbreviation.reference (encodeType signature.symbol base type)) = some type := by
    rw [baseEq, expandEquivalence_encodeType_of_fixed signature.symbol abbreviation.reference distinct
      (fun _ : Unit => .var 0) (fun _ => by simp [expandEquivalence])]
    exact readType_encode signature.symbol signature.symbol_injective type
  have bodyRead := HOLKernelAlphaReadback.encoded_body_read abbreviation profile distinct dictionary indices parameters lookup bounded
    base constant baseEq constantEq rho names assignment assignmentEq binders bindersInjective bindersAbove body depth nodup namesAbove
    (by
      intro offset less type index
      exact BinderNames.ne_nameOf_of_not_mem names (sourceNames offset (by omega)) (rho index))
  have resultRead := HOLKernelAlphaReadback.encoded_read abbreviation profile distinct dictionary indices parameters lookup bounded
    base constant baseEq constantEq rho names assignment assignmentEq binders bindersInjective bindersAbove (instantiate argument body) (depth + 1) nodup namesAbove
    (by
      intro offset less type index
      have height := Term.binderDepth_subst_le body (Subst.single argument)
      have absent := sourceNames (offset + 1) (by change offset < (HOL.subst (Subst.single argument) body).binderDepth at less; omega)
      apply BinderNames.ne_nameOf_of_not_mem names _ (rho index)
      simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using absent)
  have freshName : HOLKernelBindingInterpretation.freshName parameters names (binders depth) = true := by
    simp [HOLKernelBindingInterpretation.freshName, bindersAbove, headLookup]
  have admitted := HOLKernelQuantifierReadback.universalElimination_admitted signature abbreviation binding antecedent _ argumentCode _ _ (binders depth)
    antecedentSorted (encodeType_sorted signature context base baseSorted domain) head argumentSorted derived.bodySorted derived.resultSorted
    (by simpa only [Nat.add_zero] using fresh 0 (by omega))
    (encodeType_independent context _ signature.symbol base (baseIndependent depth) domain)
    argumentTyping derived.resultTyping derived.equation universal profile distinct dictionary parameters names domain
    (HOL.rename rho argument) (HOL.rename (Rename.lift rho) body) (HOL.rename rho (instantiate argument body)) g
    contextRead (typeRead domain) argumentRead bodyRead resultRead freshName headDictionary ruleAt bindingAt (bindingSelected .universalElimination)
    equationTree universalAdmitted
  exact ⟨_, admitted⟩

#print axioms universalElimination_admitted
/-- The source EXISTS construction retains its witness, instance proof and substitution receipt. -/
theorem existentialIntroduction_admitted (signature : Signature sorts terms)
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
    {gamma : Ctx Unit} {domain : Ty Unit}
    (argument : Term Const gamma domain) (body : Term Const (domain :: gamma) .prop)
    (assignment : Assignment gamma) (depth temporaryDepth : Nat)
    (antecedent argumentCode : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (argumentSorted : Preterm.HasType terms context argumentCode [] signature.ids.object)
    (assignmentSorted : ∀ {type} (index : Var gamma type),
      Preterm.HasType terms context (assignment index) [] signature.ids.object)
    (slots : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      context[binders (depth + offset)]? = some (.bound signature.ids.object))
    (temporarySlots : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument),
      context[temporary (temporaryDepth + offset)]? = some (.bound signature.ids.object))
    (fresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      ¬ Preterm.HasVar context (binders (depth + offset)) antecedent)
    (equationFresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument),
      ¬ Preterm.HasVar context (binders (depth + 1 + offset))
        (conjunction signature.symbol antecedent
          (holds signature.symbol (equality signature.symbol (encodeType signature.symbol base domain)
            (.var (binders depth)) argumentCode))))
    (temporaryFresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument),
      ¬ Preterm.HasVar context (temporary (temporaryDepth + offset))
        (conjunction signature.symbol antecedent
          (holds signature.symbol (equality signature.symbol (encodeType signature.symbol base domain)
            (.var (binders depth)) argumentCode))))
    (disjoint : ∀ firstOffset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument),
      ∀ secondOffset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument),
        binders (depth + 1 + firstOffset) ≠ temporary (temporaryDepth + secondOffset))
    (variableTyping : ∀ {type} (index : Var gamma type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
        (context := context) (hypotheses := [])
        (typed signature.symbol antecedent (assignment index) (encodeType signature.symbol base type)))
    (constantTyping : ∀ {type} (symbol : Const type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
        (context := context) (hypotheses := [])
        (typed signature.symbol antecedent (constant symbol) (encodeType signature.symbol base type)))
    (argumentTyping : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := [])
      (typed signature.symbol antecedent argumentCode (encodeType signature.symbol base domain)))
    (argumentEquation : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := [])
      (entails signature.symbol antecedent (holds signature.symbol
        (equality signature.symbol (encodeType signature.symbol base domain) argumentCode
          (encodeWithAssignment signature.symbol base constant binders assignment (depth + 1) argument)))))
    (instanceProof : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := [])
      (entails signature.symbol antecedent (holds signature.symbol
        (encodeWithAssignment signature.symbol base constant binders assignment (depth + 1) (instantiate argument body)))))
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
    (sourceNames : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1, binders (depth + offset) ∉ names.toList)
    (temporaryNames : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument), temporary (temporaryDepth + offset) ∉ names.toList)
    (dictionaryFresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1, dictionary (binders (depth + offset)) = none)
    (temporaryApartHead : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument), temporary (temporaryDepth + offset) ≠ binders depth)
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
      argumentEquation.val (.imp g.formula (.eq (HOL.rename rho argument) (HOL.rename rho argument))))
    {instanceFuel : Nat}
    (instanceAdmitted : AdmittedProof abbreviation theorems context
      (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) parameters ruleAt bindingAt instanceFuel names instanceProof.val
      (.imp g.formula (HOL.rename rho (instantiate argument body)))) :
    ∃ fuel, Nonempty (AdmittedProof abbreviation theorems context
      (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) parameters ruleAt bindingAt fuel names
      (HOLKernelSourceInstantiation.existentialIntroduction signature abbreviation profile structural typing rules binding base constant binders temporary
        baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent argument body assignment
        depth temporaryDepth antecedent argumentCode antecedentSorted argumentSorted assignmentSorted slots temporarySlots
        fresh equationFresh temporaryFresh disjoint variableTyping constantTyping argumentTyping argumentEquation instanceProof).val
      (.imp g.formula (.ex (HOL.rename (Rename.lift rho) body)))) := by
  let derived := HOLKernelSourceInstantiation.deriveInstance signature profile structural typing rules binding base constant binders temporary
    baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent argument body
    assignment depth temporaryDepth antecedent argumentCode antecedentSorted argumentSorted assignmentSorted
    slots temporarySlots fresh equationFresh temporaryFresh disjoint variableTyping constantTyping argumentEquation
  obtain ⟨equationFuel, ⟨equationTree⟩⟩ := deriveInstance_equation_admitted signature abbreviation profile structural typing rules binding
    base constant binders temporary baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent
    argument body assignment depth temporaryDepth antecedent argumentCode antecedentSorted argumentSorted assignmentSorted
    slots temporarySlots fresh equationFresh temporaryFresh disjoint variableTyping constantTyping argumentEquation
    distinct dictionary indices parameters lookup bounded baseEq constantEq bindersAbove temporaryAbove rho names nodup namesAbove assignmentEq
    sourceNames temporaryNames dictionaryFresh temporaryApartHead g contextRead argumentRead ruleAt bindingAt selected structuralSelected bindingSelected argumentAdmitted
  have head : context[binders depth]? = some (.bound signature.ids.object) := by
    simpa only [Nat.add_zero] using slots 0 (by omega)
  have headAbsent : binders depth ∉ names.toList := by
    simpa only [Nat.add_zero] using sourceNames 0 (by omega)
  have headLookup : names.lookup? (binders depth) = none := BinderNames.lookup?_none_of_not_mem names headAbsent
  have headDictionary : dictionary (binders depth) = none := by
    simpa only [Nat.add_zero] using dictionaryFresh 0 (by omega)
  have typeRead (type : Ty Unit) : readType signature.symbol
      (expandEquivalence signature.symbol abbreviation.reference (encodeType signature.symbol base type)) = some type := by
    rw [baseEq, expandEquivalence_encodeType_of_fixed signature.symbol abbreviation.reference distinct
      (fun _ : Unit => .var 0) (fun _ => by simp [expandEquivalence])]
    exact readType_encode signature.symbol signature.symbol_injective type
  have bodyRead := HOLKernelAlphaReadback.encoded_body_read abbreviation profile distinct dictionary indices parameters lookup bounded
    base constant baseEq constantEq rho names assignment assignmentEq binders bindersInjective bindersAbove body depth nodup namesAbove
    (by
      intro offset less type index
      exact BinderNames.ne_nameOf_of_not_mem names (sourceNames offset (by omega)) (rho index))
  have resultRead := HOLKernelAlphaReadback.encoded_read abbreviation profile distinct dictionary indices parameters lookup bounded
    base constant baseEq constantEq rho names assignment assignmentEq binders bindersInjective bindersAbove (instantiate argument body) (depth + 1) nodup namesAbove
    (by
      intro offset less type index
      have height := Term.binderDepth_subst_le body (Subst.single argument)
      have absent := sourceNames (offset + 1) (by change offset < (HOL.subst (Subst.single argument) body).binderDepth at less; omega)
      apply BinderNames.ne_nameOf_of_not_mem names _ (rho index)
      simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using absent)
  have freshName : HOLKernelBindingInterpretation.freshName parameters names (binders depth) = true := by
    simp [HOLKernelBindingInterpretation.freshName, bindersAbove, headLookup]
  have admitted := HOLKernelQuantifierReadback.existentialIntroduction_admitted signature abbreviation binding antecedent _ argumentCode _ _ (binders depth)
    antecedentSorted (encodeType_sorted signature context base baseSorted domain) head argumentSorted derived.bodySorted derived.resultSorted
    (by simpa only [Nat.add_zero] using fresh 0 (by omega))
    (encodeType_independent context _ signature.symbol base (baseIndependent depth) domain)
    derived.bodyTyping argumentTyping derived.equation instanceProof profile distinct dictionary parameters names domain
    (HOL.rename rho argument) (HOL.rename (Rename.lift rho) body) (HOL.rename rho (instantiate argument body)) g
    contextRead (typeRead domain) argumentRead bodyRead resultRead freshName headDictionary ruleAt bindingAt (bindingSelected .existentialIntroduction)
    equationTree instanceAdmitted
  exact ⟨_, admitted⟩

#print axioms existentialIntroduction_admitted

/-- Canonical beta admission follows the actual three-window argument/result rebinding and native reduction. -/
theorem canonicalBeta_admitted (signature : Signature sorts terms)
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
    (assignment : Assignment gamma) (sourceDepth workDepth temporaryDepth : Nat) (antecedent : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (assignmentSorted : ∀ {type} (index : Var gamma type),
      Preterm.HasType terms context (assignment index) [] signature.ids.object)
    (sourceSlots : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      context[binders (sourceDepth + offset)]? = some (.bound signature.ids.object))
    (workSlots : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      context[binders (workDepth + offset)]? = some (.bound signature.ids.object))
    (temporarySlots : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      context[temporary (temporaryDepth + offset)]? = some (.bound signature.ids.object))
    (sourceFresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      ¬ Preterm.HasVar context (binders (sourceDepth + offset)) antecedent)
    (workFresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      ¬ Preterm.HasVar context (binders (workDepth + offset)) antecedent)
    (temporaryFresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      ¬ Preterm.HasVar context (temporary (temporaryDepth + offset)) antecedent)
    (sourceDisjoint : ∀ firstOffset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      ∀ secondOffset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
        binders (sourceDepth + firstOffset) ≠ temporary (temporaryDepth + secondOffset))
    (workDisjoint : ∀ firstOffset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      ∀ secondOffset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
        binders (workDepth + firstOffset) ≠ temporary (temporaryDepth + secondOffset))
    (equationFresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument),
      ¬ Preterm.HasVar context (binders (workDepth + 1 + offset))
        (conjunction signature.symbol antecedent
          (holds signature.symbol (equality signature.symbol (encodeType signature.symbol base domain)
            (.var (binders workDepth))
            (encodeWithAssignment signature.symbol base constant binders assignment sourceDepth argument)))))
    (equationTemporaryFresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument),
      ¬ Preterm.HasVar context (temporary (temporaryDepth + offset))
        (conjunction signature.symbol antecedent
          (holds signature.symbol (equality signature.symbol (encodeType signature.symbol base domain)
            (.var (binders workDepth))
            (encodeWithAssignment signature.symbol base constant binders assignment sourceDepth argument)))))
    (variableTyping : ∀ {type} (index : Var gamma type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
        (context := context) (hypotheses := [])
        (typed signature.symbol antecedent (assignment index) (encodeType signature.symbol base type)))
    (constantTyping : ∀ {type} (symbol : Const type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
        (context := context) (hypotheses := [])
        (typed signature.symbol antecedent (constant symbol) (encodeType signature.symbol base type)))
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
    (sourceNames : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1, binders (sourceDepth + offset) ∉ names.toList)
    (workNames : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1, binders (workDepth + offset) ∉ names.toList)
    (temporaryNames : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1, temporary (temporaryDepth + offset) ∉ names.toList)
    (dictionaryFresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1, dictionary (binders (workDepth + offset)) = none)
    (g : Judgment Const target)
    (contextRead : readJudgmentWith (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) signature.symbol names
      (expandEquivalence signature.symbol abbreviation.reference antecedent) = some g)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (selected : ∀ rule, ruleAt (rules.index rule) = some (.inference rule))
    (structuralSelected : ∀ rule, ruleAt (structural.index rule) = some (.structural rule))
    (bindingSelected : ∀ rule, bindingAt (binding.index rule) = some rule) :
    ∃ fuel, Nonempty (AdmittedProof abbreviation theorems context
      (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) parameters ruleAt bindingAt fuel names
      (HOLKernelSourceInstantiation.canonicalBeta signature profile structural typing rules binding base constant binders temporary
        baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent argument body
        assignment sourceDepth workDepth temporaryDepth antecedent antecedentSorted assignmentSorted sourceSlots workSlots
        temporarySlots sourceFresh workFresh temporaryFresh sourceDisjoint workDisjoint equationFresh equationTemporaryFresh
        variableTyping constantTyping).val
      (.imp g.formula (.eq (HOL.rename rho (.app (.lam body) argument)) (HOL.rename rho (instantiate argument body))))) := by
  let prepared := HOLKernelSourceInstantiation.deriveCanonicalInstance signature profile structural typing rules binding base constant binders temporary
    baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent argument body
    assignment sourceDepth workDepth temporaryDepth antecedent antecedentSorted assignmentSorted sourceSlots workSlots
    temporarySlots sourceFresh workFresh temporaryFresh sourceDisjoint workDisjoint equationFresh equationTemporaryFresh
    variableTyping constantTyping
  let lambdaEquation := HOLKernelAlpha.rebind signature profile structural typing rules binding base constant binders temporary
    baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent (.lam body)
    assignment sourceDepth workDepth temporaryDepth antecedent antecedentSorted assignmentSorted
    (fun offset smaller => sourceSlots offset (by simp only [Term.binderDepth] at smaller; omega))
    (fun offset smaller => workSlots offset (by simp only [Term.binderDepth] at smaller; omega))
    (fun offset smaller => temporarySlots offset (by simp only [Term.binderDepth] at smaller; omega))
    (fun offset smaller => sourceFresh offset (by simp only [Term.binderDepth] at smaller; omega))
    (fun offset smaller => workFresh offset (by simp only [Term.binderDepth] at smaller; omega))
    (fun offset smaller => temporaryFresh offset (by simp only [Term.binderDepth] at smaller; omega))
    (by
      intro first firstSmaller second secondSmaller
      simp only [Term.binderDepth] at firstSmaller secondSmaller
      exact sourceDisjoint first (by omega) second (by omega))
    (by
      intro first firstSmaller second secondSmaller
      simp only [Term.binderDepth] at firstSmaller secondSmaller
      exact Ne.symm (workDisjoint second (by omega) first (by omega)))
    variableTyping constantTyping
  have sourceLambdaSorted := encode_sorted signature context base constant binders baseSorted constantSorted (.lam body)
    assignment sourceDepth assignmentSorted (fun offset smaller => sourceSlots offset (by simp only [Term.binderDepth] at smaller; omega))
  have workLambdaSorted := encode_sorted signature context base constant binders baseSorted constantSorted (.lam body)
    assignment workDepth assignmentSorted (fun offset smaller => workSlots offset (by simp only [Term.binderDepth] at smaller; omega))
  let before := HOLKernelInferenceProofs.Native.applicationFunction signature rules
    (encodeType signature.symbol base domain) (encodeType signature.symbol base result) antecedent
    (encodeWithAssignment signature.symbol base constant binders assignment sourceDepth argument) _ _
    (encodeType_sorted signature context base baseSorted domain) (encodeType_sorted signature context base baseSorted result)
    antecedentSorted prepared.argumentSorted sourceLambdaSorted workLambdaSorted lambdaEquation prepared.argumentTyping
  have head : context[binders workDepth]? = some (.bound signature.ids.object) := by
    simpa only [Nat.add_zero] using workSlots 0 (by omega)
  let reduction := HOLKernelBindingProofs.Native.beta signature binding antecedent _ _ (binders workDepth) _ _ _
    antecedentSorted (encodeType_sorted signature context base baseSorted domain)
    (encodeType_sorted signature context base baseSorted result) head prepared.argumentSorted
    prepared.native.bodySorted prepared.native.resultSorted
    (by simpa only [Nat.add_zero] using workFresh 0 (by omega))
    (encodeType_independent context _ signature.symbol base (baseIndependent workDepth) domain)
    (encodeType_independent context _ signature.symbol base (baseIndependent workDepth) result)
    prepared.native.bodyTyping prepared.argumentTyping prepared.native.resultTyping prepared.native.equation
  have sourceApplicationSorted := signature.application context .app _
    (.cons (.regular sourceLambdaSorted) (.cons (.regular prepared.argumentSorted) .nil))
  have workApplicationSorted := signature.application context .app _
    (.cons (.regular workLambdaSorted) (.cons (.regular prepared.argumentSorted) .nil))
  let middle := HOLKernelInferenceProofs.Native.transitivity signature rules antecedent _ _ _ _ antecedentSorted
    (encodeType_sorted signature context base baseSorted result) sourceApplicationSorted workApplicationSorted
    prepared.native.resultSorted before reduction
  have imageHeight : argument.binderDepth ≤ Subst.maxBinderDepth (Subst.single argument) :=
    Subst.binderDepth_le_maxBinderDepth (Subst.single argument) .vz
  have instanceHeight := Term.binderDepth_subst_le body (Subst.single argument)
  have argumentSorted := encode_sorted signature context base constant binders baseSorted constantSorted argument
    assignment sourceDepth assignmentSorted (fun offset smaller => sourceSlots offset (by omega))
  let argumentTyping := HOLKernelTermTyping.compileWithAssignment signature structural typing base constant binders
    baseSorted constantSorted bindersInjective baseIndependent argument assignment sourceDepth antecedent
    antecedentSorted assignmentSorted (fun offset smaller => sourceSlots offset (by omega))
    (fun offset smaller => sourceFresh offset (by omega)) variableTyping constantTyping
  let argumentEquation := HOLKernelAlpha.rebind signature profile structural typing rules binding base constant binders temporary
    baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent argument
    assignment sourceDepth (workDepth + 1) temporaryDepth antecedent antecedentSorted assignmentSorted
    (fun offset smaller => sourceSlots offset (by omega))
    (by
      intro offset smaller
      have found := workSlots (offset + 1) (by omega)
      simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using found)
    (fun offset smaller => temporarySlots offset (by omega))
    (fun offset smaller => sourceFresh offset (by omega))
    (by
      intro offset smaller
      have independent := workFresh (offset + 1) (by omega)
      simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using independent)
    (fun offset smaller => temporaryFresh offset (by omega))
    (by intro first firstSmaller second secondSmaller; exact sourceDisjoint first (by omega) second (by omega))
    (by
      intro first firstSmaller second secondSmaller
      have apart := Ne.symm (workDisjoint (second + 1) (by omega) first (by omega))
      simpa only [Nat.add_assoc, Nat.add_comm 1 second] using apart)
    variableTyping constantTyping
  let after := HOLKernelAlpha.rebind signature profile structural typing rules binding base constant binders temporary
    baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent
    (instantiate argument body) assignment (workDepth + 1) sourceDepth temporaryDepth antecedent antecedentSorted assignmentSorted
    (by
      intro offset smaller
      simp only [instantiate] at smaller
      have found := workSlots (offset + 1) (by omega)
      simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using found)
    (by intro offset smaller; simp only [instantiate] at smaller; exact sourceSlots offset (by omega))
    (by intro offset smaller; simp only [instantiate] at smaller; exact temporarySlots offset (by omega))
    (by
      intro offset smaller
      simp only [instantiate] at smaller
      have independent := workFresh (offset + 1) (by omega)
      simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using independent)
    (by intro offset smaller; simp only [instantiate] at smaller; exact sourceFresh offset (by omega))
    (by intro offset smaller; simp only [instantiate] at smaller; exact temporaryFresh offset (by omega))
    (by
      intro first firstSmaller second secondSmaller
      simp only [instantiate] at firstSmaller secondSmaller
      have apart := workDisjoint (first + 1) (by omega) second (by omega)
      simpa only [Nat.add_assoc, Nat.add_comm 1 first] using apart)
    (by
      intro first firstSmaller second secondSmaller
      simp only [instantiate] at firstSmaller secondSmaller
      exact Ne.symm (sourceDisjoint second (by omega) first (by omega)))
    variableTyping constantTyping
  have typeRead (type : Ty Unit) : readType signature.symbol
      (expandEquivalence signature.symbol abbreviation.reference (encodeType signature.symbol base type)) = some type := by
    rw [baseEq, expandEquivalence_encodeType_of_fixed signature.symbol abbreviation.reference distinct
      (fun _ : Unit => .var 0) (fun _ => by simp [expandEquivalence])]
    exact readType_encode signature.symbol signature.symbol_injective type
  have readAt {type : Ty Unit} (term : Term Const gamma type) (level : Nat)
      (free : ∀ offset < term.binderDepth, binders (level + offset) ∉ names.toList) :
      HOLKernelLogicalFunctionReadback.reader profile dictionary parameters names
        (expandEquivalence signature.symbol abbreviation.reference (encodeWithAssignment signature.symbol base constant binders assignment level term)) =
      some ⟨type, HOL.rename rho term⟩ :=
    HOLKernelAlphaReadback.encoded_read abbreviation profile distinct dictionary indices parameters lookup bounded base constant baseEq constantEq
      rho names assignment assignmentEq binders bindersInjective bindersAbove term level nodup namesAbove
      (fun offset less {_} index => BinderNames.ne_nameOf_of_not_mem names (free offset less) (rho index))
  have argumentRead := readAt argument sourceDepth (fun offset less => sourceNames offset (by omega))
  have sourceLambdaRead := readAt (.lam body) sourceDepth
    (fun offset less => sourceNames offset (by simp only [Term.binderDepth] at less; omega))
  have workLambdaRead := readAt (.lam body) workDepth
    (fun offset less => workNames offset (by simp only [Term.binderDepth] at less; omega))
  have sourceResultRead := readAt (instantiate argument body) sourceDepth
    (fun offset less => sourceNames offset (by change offset < (HOL.subst (Subst.single argument) body).binderDepth at less; omega))
  have workResultRead := readAt (instantiate argument body) (workDepth + 1) (by
    intro offset less
    have absent := workNames (offset + 1) (by change offset < (HOL.subst (Subst.single argument) body).binderDepth at less; omega)
    simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using absent)
  have argumentStable : AdmissionUnderRenaming (context := context) abbreviation profile dictionary parameters ruleAt bindingAt names
      argumentEquation.val (.imp g.formula (.eq (HOL.rename rho argument) (HOL.rename rho argument))) := by
    intro futureContext rhoNext future futureNodup futureAbove futureLookup
    apply HOLKernelAlphaReadback.rebind_admission_under_renaming signature abbreviation profile structural typing rules binding
      distinct dictionary indices parameters lookup bounded base constant baseEq constantEq binders temporary baseSorted constantSorted
      bindersInjective temporaryInjective bindersAbove temporaryAbove baseIndependent temporaryIndependent argument assignment sourceDepth (workDepth + 1) temporaryDepth
      antecedent antecedentSorted assignmentSorted _ _ _ _ _ _ _ _ variableTyping constantTyping rho names nodup assignmentEq
      _ _ _ g contextRead ruleAt bindingAt selected (bindingSelected .abstractionRenaming) rhoNext future futureNodup futureAbove futureLookup
    · intro offset less type index
      exact BinderNames.ne_nameOf_of_not_mem names (sourceNames offset (by omega)) (rho index)
    · intro offset less type index
      have absent := workNames (offset + 1) (by omega)
      apply BinderNames.ne_nameOf_of_not_mem names _ (rho index)
      simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using absent
    · intro offset less type index
      exact BinderNames.ne_nameOf_of_not_mem names (temporaryNames offset (by omega)) (rho index)
  obtain ⟨reductionFuel, ⟨reductionTree⟩⟩ := beta_admitted signature abbreviation profile structural typing rules binding
    base constant binders temporary baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent
    argument body assignment workDepth temporaryDepth antecedent _ antecedentSorted argumentSorted assignmentSorted
    workSlots (fun offset less => temporarySlots offset (by omega)) workFresh equationFresh equationTemporaryFresh
    (by
      intro first firstLess second secondLess
      have apart := workDisjoint (first + 1) (by omega) second (by omega)
      simpa only [Nat.add_assoc, Nat.add_comm 1 first] using apart)
    variableTyping constantTyping argumentTyping argumentEquation
    distinct dictionary indices parameters lookup bounded baseEq constantEq bindersAbove temporaryAbove rho names nodup namesAbove assignmentEq
    workNames (fun offset less => temporaryNames offset (by omega)) dictionaryFresh
    (by intro offset less; exact Ne.symm (by simpa only [Nat.add_zero] using workDisjoint 0 (by omega) offset (by omega)))
    g contextRead argumentRead ruleAt bindingAt selected structuralSelected bindingSelected argumentStable
  have reductionWitness : reduction.val =
      (HOLKernelSourceInstantiation.beta signature profile structural typing rules binding base constant binders temporary
        baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent argument body
        assignment workDepth temporaryDepth antecedent _ antecedentSorted argumentSorted assignmentSorted workSlots
        (fun offset less => temporarySlots offset (by omega)) workFresh equationFresh equationTemporaryFresh
        (by
          intro first firstLess second secondLess
          have apart := workDisjoint (first + 1) (by omega) second (by omega)
          simpa only [Nat.add_assoc, Nat.add_comm 1 first] using apart)
        variableTyping constantTyping argumentTyping argumentEquation).val := rfl
  rw [← reductionWitness] at reductionTree
  obtain ⟨lambdaFuel, ⟨lambdaTree⟩⟩ := HOLKernelAlphaReadback.rebind_admitted signature abbreviation profile structural typing rules binding
    distinct dictionary indices parameters lookup bounded base constant baseEq constantEq binders temporary baseSorted constantSorted
    bindersInjective temporaryInjective bindersAbove temporaryAbove baseIndependent temporaryIndependent (.lam body)
    assignment sourceDepth workDepth temporaryDepth antecedent antecedentSorted assignmentSorted
    _ _ _ _ _ _ _ _ variableTyping constantTyping rho names nodup namesAbove assignmentEq
    (by intro offset less type index; exact BinderNames.ne_nameOf_of_not_mem names (sourceNames offset (by simp only [Term.binderDepth] at less; omega)) (rho index))
    (by intro offset less type index; exact BinderNames.ne_nameOf_of_not_mem names (workNames offset (by simp only [Term.binderDepth] at less; omega)) (rho index))
    (by intro offset less type index; exact BinderNames.ne_nameOf_of_not_mem names (temporaryNames offset (by simp only [Term.binderDepth] at less; omega)) (rho index))
    g contextRead ruleAt bindingAt selected (bindingSelected .abstractionRenaming)
  obtain ⟨beforeTree⟩ := HOLKernelCongruenceReadback.applicationFunction_admitted signature abbreviation profile distinct dictionary parameters rules names
    _ _ antecedent _ _ _ (encodeType_sorted signature context base baseSorted domain) (encodeType_sorted signature context base baseSorted result)
    antecedentSorted prepared.argumentSorted sourceLambdaSorted workLambdaSorted lambdaEquation prepared.argumentTyping
    g (HOL.rename rho argument) (HOL.rename rho (.lam body)) (HOL.rename rho (.lam body)) contextRead (typeRead domain) (typeRead result)
    argumentRead sourceLambdaRead workLambdaRead ruleAt bindingAt (selected .applicationFunction) lambdaTree
  obtain ⟨afterFuel, ⟨afterTree⟩⟩ := HOLKernelAlphaReadback.rebind_admitted signature abbreviation profile structural typing rules binding
    distinct dictionary indices parameters lookup bounded base constant baseEq constantEq binders temporary baseSorted constantSorted
    bindersInjective temporaryInjective bindersAbove temporaryAbove baseIndependent temporaryIndependent (instantiate argument body)
    assignment (workDepth + 1) sourceDepth temporaryDepth antecedent antecedentSorted assignmentSorted
    _ _ _ _ _ _ _ _ variableTyping constantTyping rho names nodup namesAbove assignmentEq
    (by
      intro offset less type index
      have absent := workNames (offset + 1) (by change offset < (HOL.subst (Subst.single argument) body).binderDepth at less; omega)
      apply BinderNames.ne_nameOf_of_not_mem names _ (rho index)
      simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using absent)
    (by intro offset less type index; exact BinderNames.ne_nameOf_of_not_mem names (sourceNames offset (by change offset < (HOL.subst (Subst.single argument) body).binderDepth at less; omega)) (rho index))
    (by intro offset less type index; exact BinderNames.ne_nameOf_of_not_mem names (temporaryNames offset (by change offset < (HOL.subst (Subst.single argument) body).binderDepth at less; omega)) (rho index))
    g contextRead ruleAt bindingAt selected (bindingSelected .abstractionRenaming)
  have sourceApplicationRead := readAt (.app (.lam body) argument) sourceDepth
    (fun offset less => sourceNames offset (by simp only [Term.binderDepth] at less; omega))
  have workApplicationRead : HOLKernelLogicalFunctionReadback.reader profile dictionary parameters names
      (expandEquivalence signature.symbol abbreviation.reference
        (applySymbol signature.symbol .app [encodeWithAssignment signature.symbol base constant binders assignment workDepth (.lam body),
          encodeWithAssignment signature.symbol base constant binders assignment sourceDepth argument])) =
      some ⟨result, HOL.rename rho (.app (.lam body) argument)⟩ := by
    simp only [applySymbol, Preterm.applyArgs, expandEquivalence, if_neg (distinct .app)]
    exact readTermWith_application (HOLKernelLogicalFunctionReadback.atoms profile) signature.symbol signature.symbol_injective dictionary parameters
      names _ _ (HOL.rename rho (.lam body)) (HOL.rename rho argument) workLambdaRead argumentRead
  obtain ⟨middleTree⟩ := HOLKernelCongruenceReadback.transitivity_admitted signature abbreviation profile distinct dictionary parameters rules names
    antecedent _ _ _ _ antecedentSorted (encodeType_sorted signature context base baseSorted result) sourceApplicationSorted workApplicationSorted
    prepared.native.resultSorted before reduction g (HOL.rename rho (.app (.lam body) argument)) (HOL.rename rho (.app (.lam body) argument))
    (HOL.rename rho (instantiate argument body)) contextRead (typeRead result) sourceApplicationRead workApplicationRead workResultRead
    ruleAt bindingAt (selected .transitivity) beforeTree reductionTree
  have afterWitness : prepared.resultEquation.val = after.val := rfl
  rw [← afterWitness] at afterTree
  refine ⟨max (max (max lambdaFuel 1 + 1) reductionFuel + 1) afterFuel + 1, ?_⟩
  exact HOLKernelCongruenceReadback.transitivity_admitted signature abbreviation profile distinct dictionary parameters rules names
    antecedent _ _ _ _ antecedentSorted (encodeType_sorted signature context base baseSorted result) sourceApplicationSorted prepared.native.resultSorted
    prepared.sourceResultSorted middle prepared.resultEquation g (HOL.rename rho (.app (.lam body) argument))
    (HOL.rename rho (instantiate argument body)) (HOL.rename rho (instantiate argument body)) contextRead (typeRead result)
    sourceApplicationRead workResultRead sourceResultRead ruleAt bindingAt (selected .transitivity) middleTree afterTree

#print axioms canonicalBeta_admitted

/-- Both actual receipts of one canonical instance package retain independent admission at their respective source frames. -/
theorem deriveCanonicalInstance_admitted (signature : Signature sorts terms)
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
    (assignment : Assignment gamma) (sourceDepth workDepth temporaryDepth : Nat) (antecedent : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (assignmentSorted : ∀ {type} (index : Var gamma type),
      Preterm.HasType terms context (assignment index) [] signature.ids.object)
    (sourceSlots : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      context[binders (sourceDepth + offset)]? = some (.bound signature.ids.object))
    (workSlots : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      context[binders (workDepth + offset)]? = some (.bound signature.ids.object))
    (temporarySlots : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      context[temporary (temporaryDepth + offset)]? = some (.bound signature.ids.object))
    (sourceFresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      ¬ Preterm.HasVar context (binders (sourceDepth + offset)) antecedent)
    (workFresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      ¬ Preterm.HasVar context (binders (workDepth + offset)) antecedent)
    (temporaryFresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      ¬ Preterm.HasVar context (temporary (temporaryDepth + offset)) antecedent)
    (sourceDisjoint : ∀ firstOffset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      ∀ secondOffset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
        binders (sourceDepth + firstOffset) ≠ temporary (temporaryDepth + secondOffset))
    (workDisjoint : ∀ firstOffset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      ∀ secondOffset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
        binders (workDepth + firstOffset) ≠ temporary (temporaryDepth + secondOffset))
    (equationFresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument),
      ¬ Preterm.HasVar context (binders (workDepth + 1 + offset))
        (conjunction signature.symbol antecedent
          (holds signature.symbol (equality signature.symbol (encodeType signature.symbol base domain)
            (.var (binders workDepth))
            (encodeWithAssignment signature.symbol base constant binders assignment sourceDepth argument)))))
    (equationTemporaryFresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument),
      ¬ Preterm.HasVar context (temporary (temporaryDepth + offset))
        (conjunction signature.symbol antecedent
          (holds signature.symbol (equality signature.symbol (encodeType signature.symbol base domain)
            (.var (binders workDepth))
            (encodeWithAssignment signature.symbol base constant binders assignment sourceDepth argument)))))
    (variableTyping : ∀ {type} (index : Var gamma type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
        (context := context) (hypotheses := [])
        (typed signature.symbol antecedent (assignment index) (encodeType signature.symbol base type)))
    (constantTyping : ∀ {type} (symbol : Const type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
        (context := context) (hypotheses := [])
        (typed signature.symbol antecedent (constant symbol) (encodeType signature.symbol base type)))
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
    (sourceNames : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1, binders (sourceDepth + offset) ∉ names.toList)
    (workNames : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1, binders (workDepth + offset) ∉ names.toList)
    (temporaryNames : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1, temporary (temporaryDepth + offset) ∉ names.toList)
    (dictionaryFresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1, dictionary (binders (workDepth + offset)) = none)
    (g : Judgment Const target)
    (contextRead : readJudgmentWith (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) signature.symbol names
      (expandEquivalence signature.symbol abbreviation.reference antecedent) = some g)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (selected : ∀ rule, ruleAt (rules.index rule) = some (.inference rule))
    (structuralSelected : ∀ rule, ruleAt (structural.index rule) = some (.structural rule))
    (bindingSelected : ∀ rule, bindingAt (binding.index rule) = some rule) :
    let prepared := HOLKernelSourceInstantiation.deriveCanonicalInstance signature profile structural typing rules binding base constant binders temporary
        baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent argument body
        assignment sourceDepth workDepth temporaryDepth antecedent antecedentSorted assignmentSorted sourceSlots workSlots
        temporarySlots sourceFresh workFresh temporaryFresh sourceDisjoint workDisjoint equationFresh equationTemporaryFresh
        variableTyping constantTyping
    ∃ equationFuel resultFuel,
      Nonempty (AdmittedProof abbreviation theorems context
        (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) parameters ruleAt bindingAt equationFuel
        (BinderNames.cons (type := domain) (binders workDepth) names) prepared.native.equation.val
        (.imp (.and (weaken (σ := domain) g.formula) (.eq (.var .vz) (weaken (σ := domain) (HOL.rename rho argument))))
          (.eq (HOL.rename (Rename.lift rho) body) (weaken (σ := domain) (HOL.rename rho (instantiate argument body)))))) ∧
      Nonempty (AdmittedProof abbreviation theorems context
        (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) parameters ruleAt bindingAt resultFuel names prepared.resultEquation.val
        (.imp g.formula (.eq (HOL.rename rho (instantiate argument body)) (HOL.rename rho (instantiate argument body))))) := by
  dsimp only
  let prepared := HOLKernelSourceInstantiation.deriveCanonicalInstance signature profile structural typing rules binding base constant binders temporary
        baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent argument body
        assignment sourceDepth workDepth temporaryDepth antecedent antecedentSorted assignmentSorted sourceSlots workSlots
        temporarySlots sourceFresh workFresh temporaryFresh sourceDisjoint workDisjoint equationFresh equationTemporaryFresh
        variableTyping constantTyping
  have imageHeight : argument.binderDepth ≤ Subst.maxBinderDepth (Subst.single argument) :=
    Subst.binderDepth_le_maxBinderDepth (Subst.single argument) .vz
  have instanceHeight := Term.binderDepth_subst_le body (Subst.single argument)
  have argumentSorted := encode_sorted signature context base constant binders baseSorted constantSorted argument
    assignment sourceDepth assignmentSorted (fun offset smaller => sourceSlots offset (by omega))
  let argumentTyping := HOLKernelTermTyping.compileWithAssignment signature structural typing base constant binders
    baseSorted constantSorted bindersInjective baseIndependent argument assignment sourceDepth antecedent
    antecedentSorted assignmentSorted (fun offset smaller => sourceSlots offset (by omega))
    (fun offset smaller => sourceFresh offset (by omega)) variableTyping constantTyping
  let argumentEquation := HOLKernelAlpha.rebind signature profile structural typing rules binding base constant binders temporary
    baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent argument
    assignment sourceDepth (workDepth + 1) temporaryDepth antecedent antecedentSorted assignmentSorted
    (fun offset smaller => sourceSlots offset (by omega))
    (by
      intro offset smaller
      have found := workSlots (offset + 1) (by omega)
      simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using found)
    (fun offset smaller => temporarySlots offset (by omega))
    (fun offset smaller => sourceFresh offset (by omega))
    (by
      intro offset smaller
      have independent := workFresh (offset + 1) (by omega)
      simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using independent)
    (fun offset smaller => temporaryFresh offset (by omega))
    (by intro first firstSmaller second secondSmaller; exact sourceDisjoint first (by omega) second (by omega))
    (by
      intro first firstSmaller second secondSmaller
      have apart := Ne.symm (workDisjoint (second + 1) (by omega) first (by omega))
      simpa only [Nat.add_assoc, Nat.add_comm 1 second] using apart)
    variableTyping constantTyping
  let derived := HOLKernelSourceInstantiation.deriveInstance signature profile structural typing rules binding base constant binders temporary
    baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent argument body
    assignment workDepth temporaryDepth antecedent
    (encodeWithAssignment signature.symbol base constant binders assignment sourceDepth argument)
    antecedentSorted argumentSorted assignmentSorted workSlots
    (fun offset smaller => temporarySlots offset (by omega)) workFresh equationFresh equationTemporaryFresh
    (by
      intro first firstSmaller second secondSmaller
      have apart := workDisjoint (first + 1) (by omega) second (by omega)
      simpa only [Nat.add_assoc, Nat.add_comm 1 first] using apart)
    variableTyping constantTyping argumentEquation
  let after := HOLKernelAlpha.rebind signature profile structural typing rules binding base constant binders temporary
    baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent
    (instantiate argument body) assignment (workDepth + 1) sourceDepth temporaryDepth antecedent antecedentSorted assignmentSorted
    (by
      intro offset smaller
      simp only [instantiate] at smaller
      have found := workSlots (offset + 1) (by omega)
      simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using found)
    (by intro offset smaller; simp only [instantiate] at smaller; exact sourceSlots offset (by omega))
    (by intro offset smaller; simp only [instantiate] at smaller; exact temporarySlots offset (by omega))
    (by
      intro offset smaller
      simp only [instantiate] at smaller
      have independent := workFresh (offset + 1) (by omega)
      simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using independent)
    (by intro offset smaller; simp only [instantiate] at smaller; exact sourceFresh offset (by omega))
    (by intro offset smaller; simp only [instantiate] at smaller; exact temporaryFresh offset (by omega))
    (by
      intro first firstSmaller second secondSmaller
      simp only [instantiate] at firstSmaller secondSmaller
      have apart := workDisjoint (first + 1) (by omega) second (by omega)
      simpa only [Nat.add_assoc, Nat.add_comm 1 first] using apart)
    (by
      intro first firstSmaller second secondSmaller
      simp only [instantiate] at firstSmaller secondSmaller
      exact Ne.symm (sourceDisjoint second (by omega) first (by omega)))
    variableTyping constantTyping
  have sourceResultSorted := encode_sorted signature context base constant binders baseSorted constantSorted
    (instantiate argument body) assignment sourceDepth assignmentSorted
    (by intro offset smaller; simp only [instantiate] at smaller; exact sourceSlots offset (by omega))
  have readAt {type : Ty Unit} (term : Term Const gamma type) (level : Nat)
      (free : ∀ offset < term.binderDepth, binders (level + offset) ∉ names.toList) :
      HOLKernelLogicalFunctionReadback.reader profile dictionary parameters names
        (expandEquivalence signature.symbol abbreviation.reference (encodeWithAssignment signature.symbol base constant binders assignment level term)) =
      some ⟨type, HOL.rename rho term⟩ :=
    HOLKernelAlphaReadback.encoded_read abbreviation profile distinct dictionary indices parameters lookup bounded base constant baseEq constantEq
      rho names assignment assignmentEq binders bindersInjective bindersAbove term level nodup namesAbove
      (fun offset less {_} index => BinderNames.ne_nameOf_of_not_mem names (free offset less) (rho index))
  have argumentRead := readAt argument sourceDepth (fun offset less => sourceNames offset (by omega))
  have argumentStable : AdmissionUnderRenaming (context := context) abbreviation profile dictionary parameters ruleAt bindingAt names
      argumentEquation.val (.imp g.formula (.eq (HOL.rename rho argument) (HOL.rename rho argument))) := by
    intro futureContext rhoNext future futureNodup futureAbove futureLookup
    apply HOLKernelAlphaReadback.rebind_admission_under_renaming signature abbreviation profile structural typing rules binding
      distinct dictionary indices parameters lookup bounded base constant baseEq constantEq binders temporary baseSorted constantSorted
      bindersInjective temporaryInjective bindersAbove temporaryAbove baseIndependent temporaryIndependent argument assignment sourceDepth (workDepth + 1) temporaryDepth
      antecedent antecedentSorted assignmentSorted _ _ _ _ _ _ _ _ variableTyping constantTyping rho names nodup assignmentEq
      _ _ _ g contextRead ruleAt bindingAt selected (bindingSelected .abstractionRenaming) rhoNext future futureNodup futureAbove futureLookup
    · intro offset less type index
      exact BinderNames.ne_nameOf_of_not_mem names (sourceNames offset (by omega)) (rho index)
    · intro offset less type index
      have absent := workNames (offset + 1) (by omega)
      apply BinderNames.ne_nameOf_of_not_mem names _ (rho index)
      simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using absent
    · intro offset less type index
      exact BinderNames.ne_nameOf_of_not_mem names (temporaryNames offset (by omega)) (rho index)

  obtain ⟨equationFuel, ⟨equationTree⟩⟩ := deriveInstance_equation_admitted signature abbreviation profile structural typing rules binding
    base constant binders temporary baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent
    argument body assignment workDepth temporaryDepth antecedent _ antecedentSorted argumentSorted assignmentSorted
    workSlots (fun offset less => temporarySlots offset (by omega)) workFresh equationFresh equationTemporaryFresh
    (by
      intro first firstLess second secondLess
      have apart := workDisjoint (first + 1) (by omega) second (by omega)
      simpa only [Nat.add_assoc, Nat.add_comm 1 first] using apart)
    variableTyping constantTyping argumentEquation
    distinct dictionary indices parameters lookup bounded baseEq constantEq bindersAbove temporaryAbove rho names nodup namesAbove assignmentEq
    workNames (fun offset less => temporaryNames offset (by omega)) dictionaryFresh
    (by intro offset less; exact Ne.symm (by simpa only [Nat.add_zero] using workDisjoint 0 (by omega) offset (by omega)))
    g contextRead argumentRead ruleAt bindingAt selected structuralSelected bindingSelected argumentStable
  obtain ⟨afterFuel, ⟨afterTree⟩⟩ := HOLKernelAlphaReadback.rebind_admitted signature abbreviation profile structural typing rules binding
    distinct dictionary indices parameters lookup bounded base constant baseEq constantEq binders temporary baseSorted constantSorted
    bindersInjective temporaryInjective bindersAbove temporaryAbove baseIndependent temporaryIndependent (instantiate argument body)
    assignment (workDepth + 1) sourceDepth temporaryDepth antecedent antecedentSorted assignmentSorted
    _ _ _ _ _ _ _ _ variableTyping constantTyping rho names nodup namesAbove assignmentEq
    (by
      intro offset less type index
      have absent := workNames (offset + 1) (by change offset < (HOL.subst (Subst.single argument) body).binderDepth at less; omega)
      apply BinderNames.ne_nameOf_of_not_mem names _ (rho index)
      simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using absent)
    (by intro offset less type index; exact BinderNames.ne_nameOf_of_not_mem names (sourceNames offset (by change offset < (HOL.subst (Subst.single argument) body).binderDepth at less; omega)) (rho index))
    (by intro offset less type index; exact BinderNames.ne_nameOf_of_not_mem names (temporaryNames offset (by change offset < (HOL.subst (Subst.single argument) body).binderDepth at less; omega)) (rho index))
    g contextRead ruleAt bindingAt selected (bindingSelected .abstractionRenaming)

  have nativeWitness : prepared.native.equation.val = derived.equation.val := rfl
  have resultWitness : prepared.resultEquation.val = after.val := rfl
  refine ⟨equationFuel, afterFuel, ⟨?_⟩, ⟨?_⟩⟩
  · rw [nativeWitness]
    exact equationTree
  · rw [resultWitness]
    exact afterTree

#print axioms deriveCanonicalInstance_admitted

/-- Canonical SPEC retains formation preparation, scoped projection and both alpha rebinding receipts. -/
theorem canonicalUniversalElimination_admitted (signature : Signature sorts terms)
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
    {gamma : Ctx Unit} {domain : Ty Unit}
    (argument : Term Const gamma domain) (body : Term Const (domain :: gamma) .prop)
    (assignment : Assignment gamma) (sourceDepth workDepth temporaryDepth : Nat)
    (scope : HOLKernelStructuralRules.ProofContext terms definitions theorems context []
      signature.symbol signature.ids.wff)
    (logicalFresh : ¬ Preterm.HasVar context (binders workDepth) scope.logical)
    (assignmentSorted : ∀ {type} (index : Var gamma type),
      Preterm.HasType terms context (assignment index) [] signature.ids.object)
    (sourceSlots : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      context[binders (sourceDepth + offset)]? = some (.bound signature.ids.object))
    (workSlots : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      context[binders (workDepth + offset)]? = some (.bound signature.ids.object))
    (temporarySlots : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      context[temporary (temporaryDepth + offset)]? = some (.bound signature.ids.object))
    (sourceFresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      ¬ Preterm.HasVar context (binders (sourceDepth + offset)) scope.formation)
    (workFresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      ¬ Preterm.HasVar context (binders (workDepth + offset)) scope.formation)
    (temporaryFresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      ¬ Preterm.HasVar context (temporary (temporaryDepth + offset)) scope.formation)
    (sourceDisjoint : ∀ firstOffset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      ∀ secondOffset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
        binders (sourceDepth + firstOffset) ≠ temporary (temporaryDepth + secondOffset))
    (workDisjoint : ∀ firstOffset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      ∀ secondOffset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
        binders (workDepth + firstOffset) ≠ temporary (temporaryDepth + secondOffset))
    (equationFresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument),
      ¬ Preterm.HasVar context (binders (workDepth + 1 + offset))
        (conjunction signature.symbol scope.formation
          (holds signature.symbol (equality signature.symbol (encodeType signature.symbol base domain)
            (.var (binders workDepth))
            (encodeWithAssignment signature.symbol base constant binders assignment sourceDepth argument)))))
    (equationTemporaryFresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument),
      ¬ Preterm.HasVar context (temporary (temporaryDepth + offset))
        (conjunction signature.symbol scope.formation
          (holds signature.symbol (equality signature.symbol (encodeType signature.symbol base domain)
            (.var (binders workDepth))
            (encodeWithAssignment signature.symbol base constant binders assignment sourceDepth argument)))))
    (variableTyping : ∀ {type} (index : Var gamma type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
        (context := context) (hypotheses := [])
        (typed signature.symbol scope.formation (assignment index) (encodeType signature.symbol base type)))
    (constantTyping : ∀ {type} (symbol : Const type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
        (context := context) (hypotheses := [])
        (typed signature.symbol scope.formation (constant symbol) (encodeType signature.symbol base type)))
    (universal : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := [])
      (entails signature.symbol scope.logical (holds signature.symbol
        (encodeWithAssignment signature.symbol base constant binders assignment sourceDepth (.all body)))))
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
    (sourceNames : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1, binders (sourceDepth + offset) ∉ names.toList)
    (workNames : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1, binders (workDepth + offset) ∉ names.toList)
    (temporaryNames : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1, temporary (temporaryDepth + offset) ∉ names.toList)
    (dictionaryFresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1, dictionary (binders (workDepth + offset)) = none)
    (logical formation : Judgment Const target)
    (logicalRead : readJudgmentWith (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) signature.symbol names
      (expandEquivalence signature.symbol abbreviation.reference scope.logical) = some logical)
    (formationRead : readJudgmentWith (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) signature.symbol names
      (expandEquivalence signature.symbol abbreviation.reference scope.formation) = some formation)
    (scopeBound : scope.projection.val.VarsBelow (binders workDepth))
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (selected : ∀ rule, ruleAt (rules.index rule) = some (.inference rule))
    (structuralSelected : ∀ rule, ruleAt (structural.index rule) = some (.structural rule))
    (bindingSelected : ∀ rule, bindingAt (binding.index rule) = some rule)
    {projectionFuel universalFuel : Nat}
    (projectionAdmitted : AdmittedProof abbreviation theorems context (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters)
      parameters ruleAt bindingAt projectionFuel names scope.projection.val (.imp logical.formula formation.formula))
    (universalAdmitted : AdmittedProof abbreviation theorems context (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters)
      parameters ruleAt bindingAt universalFuel names universal.val (.imp logical.formula (.all (HOL.rename (Rename.lift rho) body)))) :
    ∃ fuel, Nonempty (AdmittedProof abbreviation theorems context (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters)
      parameters ruleAt bindingAt fuel names
      (HOLKernelSourceInstantiation.canonicalUniversalElimination signature abbreviation profile structural typing rules binding base constant binders temporary
        baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent argument body assignment
        sourceDepth workDepth temporaryDepth scope logicalFresh assignmentSorted sourceSlots workSlots temporarySlots sourceFresh workFresh
        temporaryFresh sourceDisjoint workDisjoint equationFresh equationTemporaryFresh variableTyping constantTyping universal).val
      (.imp logical.formula (HOL.rename rho (instantiate argument body)))) := by
  let antecedent := scope.formation
  have antecedentSorted := scope.formationSorted
  let formationPrepared := HOLKernelSourceInstantiation.deriveCanonicalInstance signature profile structural typing rules binding base constant binders temporary
    baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent argument body
    assignment sourceDepth workDepth temporaryDepth antecedent antecedentSorted assignmentSorted sourceSlots workSlots
    temporarySlots sourceFresh workFresh temporaryFresh sourceDisjoint workDisjoint equationFresh equationTemporaryFresh
    variableTyping constantTyping
  let formationQuantifierEquation := HOLKernelAlpha.rebind signature profile structural typing rules binding base constant binders temporary
    baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent (.all body)
    assignment sourceDepth workDepth temporaryDepth antecedent antecedentSorted assignmentSorted
    (fun offset smaller => sourceSlots offset (by simp only [Term.binderDepth] at smaller; omega))
    (fun offset smaller => workSlots offset (by simp only [Term.binderDepth] at smaller; omega))
    (fun offset smaller => temporarySlots offset (by simp only [Term.binderDepth] at smaller; omega))
    (fun offset smaller => sourceFresh offset (by simp only [Term.binderDepth] at smaller; omega))
    (fun offset smaller => workFresh offset (by simp only [Term.binderDepth] at smaller; omega))
    (fun offset smaller => temporaryFresh offset (by simp only [Term.binderDepth] at smaller; omega))
    (by
      intro first firstSmaller second secondSmaller
      simp only [Term.binderDepth] at firstSmaller secondSmaller
      exact sourceDisjoint first (by omega) second (by omega))
    (by
      intro first firstSmaller second secondSmaller
      simp only [Term.binderDepth] at firstSmaller secondSmaller
      exact Ne.symm (workDisjoint second (by omega) first (by omega)))
    variableTyping constantTyping
  have sourceQuantifierSorted := encode_sorted signature context base constant binders baseSorted constantSorted (.all body)
    assignment sourceDepth assignmentSorted (fun offset smaller => sourceSlots offset (by simp only [Term.binderDepth] at smaller; omega))
  have workQuantifierSorted := encode_sorted signature context base constant binders baseSorted constantSorted (.all body)
    assignment workDepth assignmentSorted (fun offset smaller => workSlots offset (by simp only [Term.binderDepth] at smaller; omega))
  have head : context[binders workDepth]? = some (.bound signature.ids.object) := by
    simpa only [Nat.add_zero] using workSlots 0 (by omega)
  have domainSorted := encodeType_sorted signature context base baseSorted domain
  have domainIndependent := encodeType_independent context _ signature.symbol base (baseIndependent workDepth) domain
  have propositionSorted := signature.application context .bool [] .nil
  let prepared := formationPrepared.promote signature structural scope _ _ _ _ _ _ (binders workDepth)
    domainSorted propositionSorted head
  let quantifierEquation := scope.promote signature structural _
    (holds_sorted signature context (signature.application context .eqc _
      (.cons (.regular propositionSorted) (.cons (.regular sourceQuantifierSorted) (.cons (.regular workQuantifierSorted) .nil)))))
    formationQuantifierEquation

  let universalFresh := HOLKernelInferenceProofs.booleanEqualityElimination signature abbreviation rules
    scope.logical _ _ scope.logicalSorted sourceQuantifierSorted workQuantifierSorted quantifierEquation universal
  let instanceFresh := HOLKernelQuantifierProofs.universalElimination signature abbreviation binding
    scope.logical _ _ _ _ (binders workDepth) scope.logicalSorted domainSorted head prepared.argumentSorted
    prepared.native.bodySorted prepared.native.resultSorted logicalFresh domainIndependent
    prepared.argumentTyping prepared.native.resultTyping prepared.native.equation universalFresh

  have imageHeight : argument.binderDepth ≤ Subst.maxBinderDepth (Subst.single argument) := Subst.binderDepth_le_maxBinderDepth (Subst.single argument) .vz
  have instanceHeight := Term.binderDepth_subst_le body (Subst.single argument)
  have typeRead (type : Ty Unit) : readType signature.symbol
      (expandEquivalence signature.symbol abbreviation.reference (encodeType signature.symbol base type)) = some type := by
    rw [baseEq, expandEquivalence_encodeType_of_fixed signature.symbol abbreviation.reference distinct
      (fun _ : Unit => .var 0) (fun _ => by simp [expandEquivalence])]
    exact readType_encode signature.symbol signature.symbol_injective type
  have readAt {type : Ty Unit} (term : Term Const gamma type) (level : Nat)
      (free : ∀ offset < term.binderDepth, binders (level + offset) ∉ names.toList) :
      HOLKernelLogicalFunctionReadback.reader profile dictionary parameters names
        (expandEquivalence signature.symbol abbreviation.reference (encodeWithAssignment signature.symbol base constant binders assignment level term)) =
      some ⟨type, HOL.rename rho term⟩ :=
    HOLKernelAlphaReadback.encoded_read abbreviation profile distinct dictionary indices parameters lookup bounded base constant baseEq constantEq
      rho names assignment assignmentEq binders bindersInjective bindersAbove term level nodup namesAbove
      (fun offset less {_} index => BinderNames.ne_nameOf_of_not_mem names (free offset less) (rho index))
  have argumentRead := readAt argument sourceDepth (fun offset less => sourceNames offset (by omega))
  have sourceQuantifierRead := readAt (.all body) sourceDepth
    (fun offset less => sourceNames offset (by simp only [Term.binderDepth] at less; omega))
  have workQuantifierRead := readAt (.all body) workDepth
    (fun offset less => workNames offset (by simp only [Term.binderDepth] at less; omega))
  have sourceResultRead := readAt (instantiate argument body) sourceDepth
    (fun offset less => sourceNames offset (by change offset < (HOL.subst (Subst.single argument) body).binderDepth at less; omega))
  have workResultRead := readAt (instantiate argument body) (workDepth + 1) (by
    intro offset less
    have absent := workNames (offset + 1) (by change offset < (HOL.subst (Subst.single argument) body).binderDepth at less; omega)
    simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using absent)
  obtain ⟨equationFuel, resultFuel, ⟨equationTree⟩, ⟨resultTree⟩⟩ := deriveCanonicalInstance_admitted signature abbreviation profile structural typing rules binding
    base constant binders temporary baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent argument body assignment
    sourceDepth workDepth temporaryDepth scope.formation scope.formationSorted assignmentSorted sourceSlots workSlots temporarySlots sourceFresh workFresh
    temporaryFresh sourceDisjoint workDisjoint equationFresh equationTemporaryFresh variableTyping constantTyping
    distinct dictionary indices parameters lookup bounded baseEq constantEq bindersAbove temporaryAbove rho names nodup namesAbove assignmentEq
    sourceNames workNames temporaryNames dictionaryFresh formation formationRead ruleAt bindingAt selected structuralSelected bindingSelected
  have logicalFormula : readFormulaIn abbreviation (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) parameters names scope.logical = some logical.formula := by
    simp only [readFormulaIn, logicalRead, Option.map_some]
  have formationFormula : readFormulaIn abbreviation (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) parameters names scope.formation = some formation.formula := by
    simp only [readFormulaIn, formationRead, Option.map_some]
  have resultEquationRead := HOLKernelCongruenceReadback.equation_read signature abbreviation profile distinct dictionary parameters names
    _ _ _ (HOL.rename rho (instantiate argument body)) (HOL.rename rho (instantiate argument body)) (typeRead .prop) workResultRead sourceResultRead
  obtain ⟨promotedResultTree⟩ := HOLKernelStructuralReadback.promote_admitted signature abbreviation (distinct .im) structural
    (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) parameters names ruleAt bindingAt (structuralSelected .syl) scope _
    (holds_sorted signature context (signature.application context .eqc _
      (.cons (.regular propositionSorted) (.cons (.regular formationPrepared.native.resultSorted) (.cons (.regular formationPrepared.sourceResultSorted) .nil)))))
    formationPrepared.resultEquation logical.formula formation.formula (.eq (HOL.rename rho (instantiate argument body)) (HOL.rename rho (instantiate argument body)))
    logicalFormula formationFormula resultEquationRead projectionAdmitted resultTree
  obtain ⟨quantifierFuel, ⟨quantifierTree⟩⟩ := HOLKernelAlphaReadback.rebind_admitted signature abbreviation profile structural typing rules binding
    distinct dictionary indices parameters lookup bounded base constant baseEq constantEq binders temporary baseSorted constantSorted
    bindersInjective temporaryInjective bindersAbove temporaryAbove baseIndependent temporaryIndependent (.all body) assignment sourceDepth workDepth temporaryDepth
    antecedent antecedentSorted assignmentSorted _ _ _ _ _ _ _ _ variableTyping constantTyping rho names nodup namesAbove assignmentEq
    (by intro offset less type index; exact BinderNames.ne_nameOf_of_not_mem names (sourceNames offset (by simp only [Term.binderDepth] at less; omega)) (rho index))
    (by intro offset less type index; exact BinderNames.ne_nameOf_of_not_mem names (workNames offset (by simp only [Term.binderDepth] at less; omega)) (rho index))
    (by intro offset less type index; exact BinderNames.ne_nameOf_of_not_mem names (temporaryNames offset (by simp only [Term.binderDepth] at less; omega)) (rho index))
    formation formationRead ruleAt bindingAt selected (bindingSelected .abstractionRenaming)
  have quantifierEquationRead := HOLKernelCongruenceReadback.equation_read signature abbreviation profile distinct dictionary parameters names
    _ _ _ (HOL.rename rho (.all body)) (HOL.rename rho (.all body)) (typeRead .prop) sourceQuantifierRead workQuantifierRead
  obtain ⟨promotedQuantifierTree⟩ := HOLKernelStructuralReadback.promote_admitted signature abbreviation (distinct .im) structural
    (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) parameters names ruleAt bindingAt (structuralSelected .syl) scope _ _
    formationQuantifierEquation logical.formula formation.formula (.eq (HOL.rename rho (.all body)) (HOL.rename rho (.all body)))
    logicalFormula formationFormula quantifierEquationRead projectionAdmitted quantifierTree
  obtain ⟨universalTree⟩ := HOLKernelCongruenceReadback.booleanEqualityElimination_admitted signature abbreviation profile distinct dictionary parameters
    rules names scope.logical _ _ scope.logicalSorted sourceQuantifierSorted workQuantifierSorted quantifierEquation universal logical
    (HOL.rename rho (.all body)) (HOL.rename rho (.all body)) logicalRead sourceQuantifierRead workQuantifierRead ruleAt bindingAt
    (selected .booleanEqualityElimination) promotedQuantifierTree universalAdmitted
  let nextNames : Names (domain :: target) := BinderNames.cons (binders workDepth) names
  have headAbsent : binders workDepth ∉ names.toList := by simpa only [Nat.add_zero] using workNames 0 (by omega)
  have headLookup : names.lookup? (binders workDepth) = none := BinderNames.lookup?_none_of_not_mem names headAbsent
  have headDictionary : dictionary (binders workDepth) = none := by simpa only [Nat.add_zero] using dictionaryFresh 0 (by omega)
  have nextLookup : LookupPreserving dictionary (Rename.weaken (σ := domain)) names nextNames :=
    LookupPreserving.weaken dictionary names domain (binders workDepth) headLookup headDictionary
  have nextLogicalRead := logical_judgment_rename_of_read profile dictionary parameters names nextNames (Rename.weaken (σ := domain)) nextLookup _ logical logicalRead
  have nextFormationRead := logical_judgment_rename_of_read profile dictionary parameters names nextNames (Rename.weaken (σ := domain)) nextLookup _ formation formationRead
  have nextArgumentRead := logical_reader_rename_of_read profile dictionary parameters names nextNames (Rename.weaken (σ := domain)) nextLookup _ (HOL.rename rho argument) argumentRead
  have nextResultRead := logical_reader_rename_of_read profile dictionary parameters names nextNames (Rename.weaken (σ := domain)) nextLookup _ (HOL.rename rho (instantiate argument body)) workResultRead
  have bodyRead := HOLKernelAlphaReadback.encoded_body_read abbreviation profile distinct dictionary indices parameters lookup bounded base constant baseEq constantEq
    rho names assignment assignmentEq binders bindersInjective bindersAbove body workDepth nodup namesAbove
    (by intro offset less type index; exact BinderNames.ne_nameOf_of_not_mem names (workNames offset (by omega)) (rho index))
  have nextProjection := projectionAdmitted.logical_weaken_of_varsBelow profile abbreviation dictionary parameters ruleAt bindingAt
    (binders workDepth) (Nat.le_of_lt ((List.getElem?_eq_some_iff.mp head).1)) scopeBound domain (binders workDepth) (Nat.le_refl _)
  obtain ⟨projectionTree⟩ := nextProjection
  let equalityAssumption := holds signature.symbol (equality signature.symbol (encodeType signature.symbol base domain) (.var (binders workDepth))
    (encodeWithAssignment signature.symbol base constant binders assignment sourceDepth argument))
  let instanceEquation := holds signature.symbol (equality signature.symbol (boolType signature.symbol)
    (encodeWithAssignment signature.symbol base constant binders (Assignment.extend (.var (binders workDepth)) assignment) (workDepth + 1) body)
    (encodeWithAssignment signature.symbol base constant binders assignment (workDepth + 1) (instantiate argument body)))
  have equalityAssumptionSorted : Preterm.HasType terms context equalityAssumption [] signature.ids.wff :=
    holds_sorted signature context (signature.application context .eqc _ (.cons (.regular domainSorted)
      (.cons (.regular (Preterm.HasType.var (binder := .bound signature.ids.object) head)) (.cons (.regular formationPrepared.argumentSorted) .nil))))
  have instanceEquationSorted : Preterm.HasType terms context instanceEquation [] signature.ids.wff :=
    holds_sorted signature context (signature.application context .eqc _ (.cons (.regular propositionSorted)
      (.cons (.regular formationPrepared.native.bodySorted) (.cons (.regular formationPrepared.native.resultSorted) .nil))))
  have variableRead : HOLKernelLogicalFunctionReadback.reader profile dictionary parameters nextNames
      (expandEquivalence signature.symbol abbreviation.reference (.var (binders workDepth))) = some ⟨domain, Term.var (.vz : Var (domain :: target) domain)⟩ := by
    simp [expandEquivalence, HOLKernelLogicalFunctionReadback.reader, readTermWith, readVariable, nextNames]
  have equalityAssumptionRead := HOLKernelCongruenceReadback.equation_read signature abbreviation profile distinct dictionary parameters nextNames
    _ _ _ (.var .vz) (weaken (σ := domain) (HOL.rename rho argument)) (typeRead domain) variableRead nextArgumentRead
  have instanceEquationRead := HOLKernelCongruenceReadback.equation_read signature abbreviation profile distinct dictionary parameters nextNames
    _ _ _ (HOL.rename (Rename.lift rho) body) (weaken (σ := domain) (HOL.rename rho (instantiate argument body))) (typeRead .prop) bodyRead nextResultRead
  obtain ⟨promotedEquationFuel, ⟨promotedEquationTree⟩⟩ := HOLKernelStructuralReadback.promoteUnder_admitted signature abbreviation (distinct .im) (distinct .an) structural
    (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) parameters nextNames ruleAt bindingAt structuralSelected scope equalityAssumption instanceEquation
    equalityAssumptionSorted instanceEquationSorted formationPrepared.native.equation
    (weaken (σ := domain) logical.formula) (weaken (σ := domain) formation.formula) (.eq (.var .vz) (weaken (σ := domain) (HOL.rename rho argument)))
    (.eq (HOL.rename (Rename.lift rho) body) (weaken (σ := domain) (HOL.rename rho (instantiate argument body))))
    (by simp only [readFormulaIn, nextLogicalRead, Option.map_some, Judgment.rename_formula]; rfl)
    (by simp only [readFormulaIn, nextFormationRead, Option.map_some, Judgment.rename_formula]; rfl)
    equalityAssumptionRead instanceEquationRead projectionTree equationTree
  have freshName : HOLKernelBindingInterpretation.freshName parameters names (binders workDepth) = true := by
    simp [HOLKernelBindingInterpretation.freshName, bindersAbove, headLookup]
  obtain ⟨instanceTree⟩ := HOLKernelQuantifierReadback.universalElimination_admitted signature abbreviation binding scope.logical _ _ _ _ (binders workDepth)
    scope.logicalSorted domainSorted head prepared.argumentSorted prepared.native.bodySorted prepared.native.resultSorted logicalFresh domainIndependent
    prepared.argumentTyping prepared.native.resultTyping prepared.native.equation universalFresh profile distinct dictionary parameters names domain
    (HOL.rename rho argument) (HOL.rename (Rename.lift rho) body) (HOL.rename rho (instantiate argument body)) logical logicalRead (typeRead domain)
    argumentRead bodyRead workResultRead freshName headDictionary ruleAt bindingAt (bindingSelected .universalElimination) promotedEquationTree universalTree
  have finalAdmitted := HOLKernelCongruenceReadback.booleanEqualityElimination_admitted signature abbreviation profile distinct dictionary parameters rules names
    scope.logical _ _ scope.logicalSorted prepared.native.resultSorted prepared.sourceResultSorted prepared.resultEquation instanceFresh logical
    (HOL.rename rho (instantiate argument body)) (HOL.rename rho (instantiate argument body)) logicalRead workResultRead sourceResultRead
    ruleAt bindingAt (selected .booleanEqualityElimination) promotedResultTree instanceTree
  exact ⟨_, finalAdmitted⟩

#print axioms canonicalUniversalElimination_admitted
/-- Canonical EXISTS retains the witness instance, scoped projection and both reversed output comparisons. -/
theorem canonicalExistentialIntroduction_admitted (signature : Signature sorts terms)
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
    {gamma : Ctx Unit} {domain : Ty Unit}
    (argument : Term Const gamma domain) (body : Term Const (domain :: gamma) .prop)
    (assignment : Assignment gamma) (sourceDepth workDepth temporaryDepth : Nat)
    (scope : HOLKernelStructuralRules.ProofContext terms definitions theorems context []
      signature.symbol signature.ids.wff)
    (logicalFresh : ¬ Preterm.HasVar context (binders workDepth) scope.logical)
    (assignmentSorted : ∀ {type} (index : Var gamma type),
      Preterm.HasType terms context (assignment index) [] signature.ids.object)
    (sourceSlots : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      context[binders (sourceDepth + offset)]? = some (.bound signature.ids.object))
    (workSlots : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      context[binders (workDepth + offset)]? = some (.bound signature.ids.object))
    (temporarySlots : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      context[temporary (temporaryDepth + offset)]? = some (.bound signature.ids.object))
    (sourceFresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      ¬ Preterm.HasVar context (binders (sourceDepth + offset)) scope.formation)
    (workFresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      ¬ Preterm.HasVar context (binders (workDepth + offset)) scope.formation)
    (temporaryFresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      ¬ Preterm.HasVar context (temporary (temporaryDepth + offset)) scope.formation)
    (sourceDisjoint : ∀ firstOffset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      ∀ secondOffset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
        binders (sourceDepth + firstOffset) ≠ temporary (temporaryDepth + secondOffset))
    (workDisjoint : ∀ firstOffset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      ∀ secondOffset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
        binders (workDepth + firstOffset) ≠ temporary (temporaryDepth + secondOffset))
    (equationFresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument),
      ¬ Preterm.HasVar context (binders (workDepth + 1 + offset))
        (conjunction signature.symbol scope.formation
          (holds signature.symbol (equality signature.symbol (encodeType signature.symbol base domain)
            (.var (binders workDepth))
            (encodeWithAssignment signature.symbol base constant binders assignment sourceDepth argument)))))
    (equationTemporaryFresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument),
      ¬ Preterm.HasVar context (temporary (temporaryDepth + offset))
        (conjunction signature.symbol scope.formation
          (holds signature.symbol (equality signature.symbol (encodeType signature.symbol base domain)
            (.var (binders workDepth))
            (encodeWithAssignment signature.symbol base constant binders assignment sourceDepth argument)))))
    (variableTyping : ∀ {type} (index : Var gamma type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
        (context := context) (hypotheses := [])
        (typed signature.symbol scope.formation (assignment index) (encodeType signature.symbol base type)))
    (constantTyping : ∀ {type} (symbol : Const type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
        (context := context) (hypotheses := [])
        (typed signature.symbol scope.formation (constant symbol) (encodeType signature.symbol base type)))
    (instanceProof : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := [])
      (entails signature.symbol scope.logical (holds signature.symbol
        (encodeWithAssignment signature.symbol base constant binders assignment sourceDepth
          (instantiate argument body)))))
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
    (sourceNames : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1, binders (sourceDepth + offset) ∉ names.toList)
    (workNames : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1, binders (workDepth + offset) ∉ names.toList)
    (temporaryNames : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1, temporary (temporaryDepth + offset) ∉ names.toList)
    (dictionaryFresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1, dictionary (binders (workDepth + offset)) = none)
    (logical formation : Judgment Const target)
    (logicalRead : readJudgmentWith (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) signature.symbol names
      (expandEquivalence signature.symbol abbreviation.reference scope.logical) = some logical)
    (formationRead : readJudgmentWith (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) signature.symbol names
      (expandEquivalence signature.symbol abbreviation.reference scope.formation) = some formation)
    (scopeBound : scope.projection.val.VarsBelow (binders workDepth))
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (selected : ∀ rule, ruleAt (rules.index rule) = some (.inference rule))
    (structuralSelected : ∀ rule, ruleAt (structural.index rule) = some (.structural rule))
    (bindingSelected : ∀ rule, bindingAt (binding.index rule) = some rule)
    {projectionFuel instanceFuel : Nat}
    (projectionAdmitted : AdmittedProof abbreviation theorems context (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters)
      parameters ruleAt bindingAt projectionFuel names scope.projection.val (.imp logical.formula formation.formula))
    (instanceAdmitted : AdmittedProof abbreviation theorems context (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters)
      parameters ruleAt bindingAt instanceFuel names instanceProof.val (.imp logical.formula (HOL.rename rho (instantiate argument body)))) :
    ∃ fuel, Nonempty (AdmittedProof abbreviation theorems context (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters)
      parameters ruleAt bindingAt fuel names
      (HOLKernelSourceInstantiation.canonicalExistentialIntroduction signature abbreviation profile structural typing rules binding base constant binders temporary
        baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent argument body assignment
        sourceDepth workDepth temporaryDepth scope logicalFresh assignmentSorted sourceSlots workSlots temporarySlots sourceFresh workFresh
        temporaryFresh sourceDisjoint workDisjoint equationFresh equationTemporaryFresh variableTyping constantTyping instanceProof).val
      (.imp logical.formula (.ex (HOL.rename (Rename.lift rho) body)))) := by
  let antecedent := scope.formation
  have antecedentSorted := scope.formationSorted
  let formationPrepared := HOLKernelSourceInstantiation.deriveCanonicalInstance signature profile structural typing rules binding base constant binders temporary
    baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent argument body
    assignment sourceDepth workDepth temporaryDepth antecedent antecedentSorted assignmentSorted sourceSlots workSlots
    temporarySlots sourceFresh workFresh temporaryFresh sourceDisjoint workDisjoint equationFresh equationTemporaryFresh
    variableTyping constantTyping
  let formationQuantifierEquation := HOLKernelAlpha.rebind signature profile structural typing rules binding base constant binders temporary
    baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent (.ex body)
    assignment sourceDepth workDepth temporaryDepth antecedent antecedentSorted assignmentSorted
    (fun offset smaller => sourceSlots offset (by simp only [Term.binderDepth] at smaller; omega))
    (fun offset smaller => workSlots offset (by simp only [Term.binderDepth] at smaller; omega))
    (fun offset smaller => temporarySlots offset (by simp only [Term.binderDepth] at smaller; omega))
    (fun offset smaller => sourceFresh offset (by simp only [Term.binderDepth] at smaller; omega))
    (fun offset smaller => workFresh offset (by simp only [Term.binderDepth] at smaller; omega))
    (fun offset smaller => temporaryFresh offset (by simp only [Term.binderDepth] at smaller; omega))
    (by
      intro first firstSmaller second secondSmaller
      simp only [Term.binderDepth] at firstSmaller secondSmaller
      exact sourceDisjoint first (by omega) second (by omega))
    (by
      intro first firstSmaller second secondSmaller
      simp only [Term.binderDepth] at firstSmaller secondSmaller
      exact Ne.symm (workDisjoint second (by omega) first (by omega)))
    variableTyping constantTyping
  have sourceQuantifierSorted := encode_sorted signature context base constant binders baseSorted constantSorted (.ex body)
    assignment sourceDepth assignmentSorted (fun offset smaller => sourceSlots offset (by simp only [Term.binderDepth] at smaller; omega))
  have workQuantifierSorted := encode_sorted signature context base constant binders baseSorted constantSorted (.ex body)
    assignment workDepth assignmentSorted (fun offset smaller => workSlots offset (by simp only [Term.binderDepth] at smaller; omega))
  have head : context[binders workDepth]? = some (.bound signature.ids.object) := by
    simpa only [Nat.add_zero] using workSlots 0 (by omega)
  have domainSorted := encodeType_sorted signature context base baseSorted domain
  have domainIndependent := encodeType_independent context _ signature.symbol base (baseIndependent workDepth) domain
  have propositionSorted := signature.application context .bool [] .nil
  let prepared := formationPrepared.promote signature structural scope _ _ _ _ _ _ (binders workDepth)
    domainSorted propositionSorted head
  let quantifierEquation := scope.promote signature structural _
    (holds_sorted signature context (signature.application context .eqc _
      (.cons (.regular propositionSorted) (.cons (.regular sourceQuantifierSorted) (.cons (.regular workQuantifierSorted) .nil)))))
    formationQuantifierEquation

  have boolSorted := signature.application context .bool [] .nil
  let instanceEquation := HOLKernelInferenceProofs.Native.symmetry signature rules (boolType signature.symbol) scope.logical _ _
    boolSorted scope.logicalSorted prepared.native.resultSorted prepared.sourceResultSorted prepared.resultEquation
  let instanceFresh := HOLKernelInferenceProofs.booleanEqualityElimination signature abbreviation rules
    scope.logical _ _ scope.logicalSorted prepared.sourceResultSorted prepared.native.resultSorted instanceEquation instanceProof
  let existentialFresh := HOLKernelQuantifierProofs.existentialIntroduction signature abbreviation binding
    scope.logical _ _ _ _ (binders workDepth) scope.logicalSorted domainSorted head prepared.argumentSorted
    prepared.native.bodySorted prepared.native.resultSorted logicalFresh domainIndependent
    prepared.native.bodyTyping prepared.argumentTyping prepared.native.equation instanceFresh
  let outputEquation := HOLKernelInferenceProofs.Native.symmetry signature rules (boolType signature.symbol) scope.logical _ _
    boolSorted scope.logicalSorted sourceQuantifierSorted workQuantifierSorted quantifierEquation
  have imageHeight : argument.binderDepth ≤ Subst.maxBinderDepth (Subst.single argument) := Subst.binderDepth_le_maxBinderDepth (Subst.single argument) .vz
  have instanceHeight := Term.binderDepth_subst_le body (Subst.single argument)
  have typeRead (type : Ty Unit) : readType signature.symbol
      (expandEquivalence signature.symbol abbreviation.reference (encodeType signature.symbol base type)) = some type := by
    rw [baseEq, expandEquivalence_encodeType_of_fixed signature.symbol abbreviation.reference distinct
      (fun _ : Unit => .var 0) (fun _ => by simp [expandEquivalence])]
    exact readType_encode signature.symbol signature.symbol_injective type
  have readAt {type : Ty Unit} (term : Term Const gamma type) (level : Nat)
      (free : ∀ offset < term.binderDepth, binders (level + offset) ∉ names.toList) :
      HOLKernelLogicalFunctionReadback.reader profile dictionary parameters names
        (expandEquivalence signature.symbol abbreviation.reference (encodeWithAssignment signature.symbol base constant binders assignment level term)) =
      some ⟨type, HOL.rename rho term⟩ :=
    HOLKernelAlphaReadback.encoded_read abbreviation profile distinct dictionary indices parameters lookup bounded base constant baseEq constantEq
      rho names assignment assignmentEq binders bindersInjective bindersAbove term level nodup namesAbove
      (fun offset less {_} index => BinderNames.ne_nameOf_of_not_mem names (free offset less) (rho index))
  have argumentRead := readAt argument sourceDepth (fun offset less => sourceNames offset (by omega))
  have sourceQuantifierRead := readAt (.ex body) sourceDepth
    (fun offset less => sourceNames offset (by simp only [Term.binderDepth] at less; omega))
  have workQuantifierRead := readAt (.ex body) workDepth
    (fun offset less => workNames offset (by simp only [Term.binderDepth] at less; omega))
  have sourceResultRead := readAt (instantiate argument body) sourceDepth
    (fun offset less => sourceNames offset (by change offset < (HOL.subst (Subst.single argument) body).binderDepth at less; omega))
  have workResultRead := readAt (instantiate argument body) (workDepth + 1) (by
    intro offset less
    have absent := workNames (offset + 1) (by change offset < (HOL.subst (Subst.single argument) body).binderDepth at less; omega)
    simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using absent)
  obtain ⟨equationFuel, resultFuel, ⟨equationTree⟩, ⟨resultTree⟩⟩ := deriveCanonicalInstance_admitted signature abbreviation profile structural typing rules binding
    base constant binders temporary baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent argument body assignment
    sourceDepth workDepth temporaryDepth scope.formation scope.formationSorted assignmentSorted sourceSlots workSlots temporarySlots sourceFresh workFresh
    temporaryFresh sourceDisjoint workDisjoint equationFresh equationTemporaryFresh variableTyping constantTyping
    distinct dictionary indices parameters lookup bounded baseEq constantEq bindersAbove temporaryAbove rho names nodup namesAbove assignmentEq
    sourceNames workNames temporaryNames dictionaryFresh formation formationRead ruleAt bindingAt selected structuralSelected bindingSelected
  have logicalFormula : readFormulaIn abbreviation (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) parameters names scope.logical = some logical.formula := by
    simp only [readFormulaIn, logicalRead, Option.map_some]
  have formationFormula : readFormulaIn abbreviation (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) parameters names scope.formation = some formation.formula := by
    simp only [readFormulaIn, formationRead, Option.map_some]
  have resultEquationRead := HOLKernelCongruenceReadback.equation_read signature abbreviation profile distinct dictionary parameters names
    _ _ _ (HOL.rename rho (instantiate argument body)) (HOL.rename rho (instantiate argument body)) (typeRead .prop) workResultRead sourceResultRead
  obtain ⟨promotedResultTree⟩ := HOLKernelStructuralReadback.promote_admitted signature abbreviation (distinct .im) structural
    (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) parameters names ruleAt bindingAt (structuralSelected .syl) scope _
    (holds_sorted signature context (signature.application context .eqc _
      (.cons (.regular propositionSorted) (.cons (.regular formationPrepared.native.resultSorted) (.cons (.regular formationPrepared.sourceResultSorted) .nil)))))
    formationPrepared.resultEquation logical.formula formation.formula (.eq (HOL.rename rho (instantiate argument body)) (HOL.rename rho (instantiate argument body)))
    logicalFormula formationFormula resultEquationRead projectionAdmitted resultTree
  obtain ⟨quantifierFuel, ⟨quantifierTree⟩⟩ := HOLKernelAlphaReadback.rebind_admitted signature abbreviation profile structural typing rules binding
    distinct dictionary indices parameters lookup bounded base constant baseEq constantEq binders temporary baseSorted constantSorted
    bindersInjective temporaryInjective bindersAbove temporaryAbove baseIndependent temporaryIndependent (.ex body) assignment sourceDepth workDepth temporaryDepth
    antecedent antecedentSorted assignmentSorted _ _ _ _ _ _ _ _ variableTyping constantTyping rho names nodup namesAbove assignmentEq
    (by intro offset less type index; exact BinderNames.ne_nameOf_of_not_mem names (sourceNames offset (by simp only [Term.binderDepth] at less; omega)) (rho index))
    (by intro offset less type index; exact BinderNames.ne_nameOf_of_not_mem names (workNames offset (by simp only [Term.binderDepth] at less; omega)) (rho index))
    (by intro offset less type index; exact BinderNames.ne_nameOf_of_not_mem names (temporaryNames offset (by simp only [Term.binderDepth] at less; omega)) (rho index))
    formation formationRead ruleAt bindingAt selected (bindingSelected .abstractionRenaming)
  have quantifierEquationRead := HOLKernelCongruenceReadback.equation_read signature abbreviation profile distinct dictionary parameters names
    _ _ _ (HOL.rename rho (.ex body)) (HOL.rename rho (.ex body)) (typeRead .prop) sourceQuantifierRead workQuantifierRead
  obtain ⟨promotedQuantifierTree⟩ := HOLKernelStructuralReadback.promote_admitted signature abbreviation (distinct .im) structural
    (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) parameters names ruleAt bindingAt (structuralSelected .syl) scope _ _
    formationQuantifierEquation logical.formula formation.formula (.eq (HOL.rename rho (.ex body)) (HOL.rename rho (.ex body)))
    logicalFormula formationFormula quantifierEquationRead projectionAdmitted quantifierTree
  obtain ⟨instanceSymmetry⟩ := HOLKernelCongruenceReadback.symmetry_admitted signature abbreviation profile distinct dictionary parameters
    rules names (boolType signature.symbol) scope.logical _ _ boolSorted scope.logicalSorted prepared.native.resultSorted prepared.sourceResultSorted
    prepared.resultEquation logical (HOL.rename rho (instantiate argument body)) (HOL.rename rho (instantiate argument body)) logicalRead (typeRead .prop)
    workResultRead sourceResultRead ruleAt bindingAt (selected .symmetry) promotedResultTree
  obtain ⟨instanceTree⟩ := HOLKernelCongruenceReadback.booleanEqualityElimination_admitted signature abbreviation profile distinct dictionary parameters
    rules names scope.logical _ _ scope.logicalSorted prepared.sourceResultSorted prepared.native.resultSorted instanceEquation instanceProof logical
    (HOL.rename rho (instantiate argument body)) (HOL.rename rho (instantiate argument body)) logicalRead sourceResultRead workResultRead ruleAt bindingAt
    (selected .booleanEqualityElimination) instanceSymmetry instanceAdmitted
  let nextNames : Names (domain :: target) := BinderNames.cons (binders workDepth) names
  have headAbsent : binders workDepth ∉ names.toList := by simpa only [Nat.add_zero] using workNames 0 (by omega)
  have headLookup : names.lookup? (binders workDepth) = none := BinderNames.lookup?_none_of_not_mem names headAbsent
  have headDictionary : dictionary (binders workDepth) = none := by simpa only [Nat.add_zero] using dictionaryFresh 0 (by omega)
  have nextLookup : LookupPreserving dictionary (Rename.weaken (σ := domain)) names nextNames :=
    LookupPreserving.weaken dictionary names domain (binders workDepth) headLookup headDictionary
  have nextLogicalRead := logical_judgment_rename_of_read profile dictionary parameters names nextNames (Rename.weaken (σ := domain)) nextLookup _ logical logicalRead
  have nextFormationRead := logical_judgment_rename_of_read profile dictionary parameters names nextNames (Rename.weaken (σ := domain)) nextLookup _ formation formationRead
  have nextArgumentRead := logical_reader_rename_of_read profile dictionary parameters names nextNames (Rename.weaken (σ := domain)) nextLookup _ (HOL.rename rho argument) argumentRead
  have nextResultRead := logical_reader_rename_of_read profile dictionary parameters names nextNames (Rename.weaken (σ := domain)) nextLookup _ (HOL.rename rho (instantiate argument body)) workResultRead
  have bodyRead := HOLKernelAlphaReadback.encoded_body_read abbreviation profile distinct dictionary indices parameters lookup bounded base constant baseEq constantEq
    rho names assignment assignmentEq binders bindersInjective bindersAbove body workDepth nodup namesAbove
    (by intro offset less type index; exact BinderNames.ne_nameOf_of_not_mem names (workNames offset (by omega)) (rho index))
  have nextProjection := projectionAdmitted.logical_weaken_of_varsBelow profile abbreviation dictionary parameters ruleAt bindingAt
    (binders workDepth) (Nat.le_of_lt ((List.getElem?_eq_some_iff.mp head).1)) scopeBound domain (binders workDepth) (Nat.le_refl _)
  obtain ⟨projectionTree⟩ := nextProjection
  let equalityAssumption := holds signature.symbol (equality signature.symbol (encodeType signature.symbol base domain) (.var (binders workDepth))
    (encodeWithAssignment signature.symbol base constant binders assignment sourceDepth argument))
  let bodyEquation := holds signature.symbol (equality signature.symbol (boolType signature.symbol)
    (encodeWithAssignment signature.symbol base constant binders (Assignment.extend (.var (binders workDepth)) assignment) (workDepth + 1) body)
    (encodeWithAssignment signature.symbol base constant binders assignment (workDepth + 1) (instantiate argument body)))
  have equalityAssumptionSorted : Preterm.HasType terms context equalityAssumption [] signature.ids.wff :=
    holds_sorted signature context (signature.application context .eqc _ (.cons (.regular domainSorted)
      (.cons (.regular (Preterm.HasType.var (binder := .bound signature.ids.object) head)) (.cons (.regular formationPrepared.argumentSorted) .nil))))
  have instanceEquationSorted : Preterm.HasType terms context bodyEquation [] signature.ids.wff :=
    holds_sorted signature context (signature.application context .eqc _ (.cons (.regular propositionSorted)
      (.cons (.regular formationPrepared.native.bodySorted) (.cons (.regular formationPrepared.native.resultSorted) .nil))))
  have variableRead : HOLKernelLogicalFunctionReadback.reader profile dictionary parameters nextNames
      (expandEquivalence signature.symbol abbreviation.reference (.var (binders workDepth))) = some ⟨domain, Term.var (.vz : Var (domain :: target) domain)⟩ := by
    simp [expandEquivalence, HOLKernelLogicalFunctionReadback.reader, readTermWith, readVariable, nextNames]
  have equalityAssumptionRead := HOLKernelCongruenceReadback.equation_read signature abbreviation profile distinct dictionary parameters nextNames
    _ _ _ (.var .vz) (weaken (σ := domain) (HOL.rename rho argument)) (typeRead domain) variableRead nextArgumentRead
  have instanceEquationRead := HOLKernelCongruenceReadback.equation_read signature abbreviation profile distinct dictionary parameters nextNames
    _ _ _ (HOL.rename (Rename.lift rho) body) (weaken (σ := domain) (HOL.rename rho (instantiate argument body))) (typeRead .prop) bodyRead nextResultRead
  obtain ⟨promotedEquationFuel, ⟨promotedEquationTree⟩⟩ := HOLKernelStructuralReadback.promoteUnder_admitted signature abbreviation (distinct .im) (distinct .an) structural
    (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) parameters nextNames ruleAt bindingAt structuralSelected scope equalityAssumption bodyEquation
    equalityAssumptionSorted instanceEquationSorted formationPrepared.native.equation
    (weaken (σ := domain) logical.formula) (weaken (σ := domain) formation.formula) (.eq (.var .vz) (weaken (σ := domain) (HOL.rename rho argument)))
    (.eq (HOL.rename (Rename.lift rho) body) (weaken (σ := domain) (HOL.rename rho (instantiate argument body))))
    (by simp only [readFormulaIn, nextLogicalRead, Option.map_some, Judgment.rename_formula]; rfl)
    (by simp only [readFormulaIn, nextFormationRead, Option.map_some, Judgment.rename_formula]; rfl)
    equalityAssumptionRead instanceEquationRead projectionTree equationTree
  have freshName : HOLKernelBindingInterpretation.freshName parameters names (binders workDepth) = true := by
    simp [HOLKernelBindingInterpretation.freshName, bindersAbove, headLookup]
  obtain ⟨existentialTree⟩ := HOLKernelQuantifierReadback.existentialIntroduction_admitted signature abbreviation binding scope.logical _ _ _ _ (binders workDepth)
    scope.logicalSorted domainSorted head prepared.argumentSorted prepared.native.bodySorted prepared.native.resultSorted logicalFresh domainIndependent
    prepared.native.bodyTyping prepared.argumentTyping prepared.native.equation instanceFresh profile distinct dictionary parameters names domain
    (HOL.rename rho argument) (HOL.rename (Rename.lift rho) body) (HOL.rename rho (instantiate argument body)) logical logicalRead (typeRead domain)
    argumentRead bodyRead workResultRead freshName headDictionary ruleAt bindingAt (bindingSelected .existentialIntroduction) promotedEquationTree instanceTree
  obtain ⟨outputTree⟩ := HOLKernelCongruenceReadback.symmetry_admitted signature abbreviation profile distinct dictionary parameters rules names
    (boolType signature.symbol) scope.logical _ _ boolSorted scope.logicalSorted sourceQuantifierSorted workQuantifierSorted quantifierEquation logical
    (HOL.rename rho (.ex body)) (HOL.rename rho (.ex body)) logicalRead (typeRead .prop) sourceQuantifierRead workQuantifierRead
    ruleAt bindingAt (selected .symmetry) promotedQuantifierTree
  have finalAdmitted := HOLKernelCongruenceReadback.booleanEqualityElimination_admitted signature abbreviation profile distinct dictionary parameters rules names
    scope.logical _ _ scope.logicalSorted workQuantifierSorted sourceQuantifierSorted outputEquation existentialFresh logical
    (HOL.rename rho (.ex body)) (HOL.rename rho (.ex body)) logicalRead workQuantifierRead sourceQuantifierRead
    ruleAt bindingAt (selected .booleanEqualityElimination) outputTree existentialTree
  exact ⟨_, finalAdmitted⟩

#print axioms canonicalExistentialIntroduction_admitted

end Mettapedia.Languages.MM0.HOLKernelSourceInstantiationReadback
