import Mettapedia.Languages.MM0.Kernel.ContextExtension
import Mettapedia.Languages.MM0.HOLKernelReadbackRenaming
import Mettapedia.Languages.MM0.HOLKernelProofReadback

/-!
# Name-frame transport of independently admitted HOL proofs

All eleven binding-rule readings commute with intrinsic renaming when native
name lookup is preserved below an explicit bound. Freshness, simultaneous
substitution, lifted premises and the actual theorem authority are retained.

For complete proof trees the bound comes from checking the same native witness
in a context prefix. The checking laws bound every supplied argument and every
instantiated conclusion, including internal binding names. An admitted tree in
the extended context can then be read in a new frame agreeing on that prefix.
This is a theorem about the submitted witness; it does not infer admission
from its source derivation or assert that all compiler outputs are admitted.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.MM0.HOLKernelBindingInterpretation
open Mettapedia.Logic Mettapedia.Logic.HOL
open Kernel HOLKernelSyntax HOLKernelTermReadback HOLKernelJudgmentReadback HOLKernelRuleReadback
open NamedElaboration (BinderNames)
universe u
variable {Const : Ty Unit → Type u} {gamma delta : Ctx Unit}
variable {terms : TermSignature} {definitions : Definition.Signature}
variable {references : HOLKernelSyntax.Symbol → Nat} {ids : SortIds}

theorem freshName_rename (parameters bound name : Nat)
    (rho : Rename Unit gamma delta) (source : Names gamma) (target : Names delta)
    (related : NamesRel bound rho source target) (smaller : name < bound) :
    freshName parameters target name = freshName parameters source name := by
  simp [freshName, related name smaller]

/-- Renaming of a local binding rule retains the native name and its freshness
check, and lifts the intrinsic renaming only in the rule's bound premises. -/
def AdmittedBindingStep.rename
    {abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions references ids}
    {reader : TermReader Const} {parameters : Nat}
    {Child Next : {delta : Ctx Unit} → Names delta → ProofWitness → Formula Const delta → Type u}
    {source : Names gamma} {rule : HOLKernelBindingRules.Rule}
    {arguments : List Preterm} {children : List ProofWitness} {formula : Formula Const gamma}
    (step : AdmittedBindingStep abbreviation reader parameters Child source rule arguments children formula)
    (bound : Nat) (rho : Rename Unit gamma delta) (target : Names delta)
    (related : NamesRel bound rho source target)
    (natural : ∀ native : Preterm, Preterm.VarsBelow bound native →
      reader target native = (reader source native).map (Decoded.rename rho))
    (bounded : ∀ argument ∈ arguments, Preterm.VarsBelow bound argument)
    (transform : ∀ {first second : Ctx Unit} {oldNames : Names first} {newNames : Names second}
      {child : ProofWitness} {childFormula : Formula Const first}, child ∈ children →
      (sigma : Rename Unit first second) → NamesRel bound sigma oldNames newNames →
      Child oldNames child childFormula → Next newNames child (HOL.rename sigma childFormula)) :
    AdmittedBindingStep abbreviation reader parameters Next target rule arguments children (HOL.rename rho formula) := by
  have instantiateNatural {domain codomain : Ty Unit} (argument : Term Const gamma domain)
      (body : Term Const (domain :: gamma) codomain) :
      HOL.rename rho (HOL.subst (Subst.single argument) body) =
        HOL.subst (Subst.single (HOL.rename rho argument)) (HOL.rename (Rename.lift rho) body) :=
    ExtDerivation.rename_instantiate rho argument body
  cases step with
  | universalIntroduction fresh child =>
      refine .universalIntroduction ?_ ?_
      · rwa [freshName_rename parameters bound _ rho source target related (bounded (.var _) (by simp))]
      · simpa only [HOL.rename, ExtDerivation.rename_weaken] using
          transform (by simp) (Rename.lift rho) (related.cons _ _) child
  | abstractionCongruence fresh child =>
      refine .abstractionCongruence ?_ ?_
      · rwa [freshName_rename parameters bound _ rho source target related (bounded (.var _) (by simp))]
      · simpa only [HOL.rename, ExtDerivation.rename_weaken] using
          transform (by simp) (Rename.lift rho) (related.cons _ _) child
  | eta =>
      simpa only [HOL.rename, ExtDerivation.rename_weaken, Rename.lift] using
        (AdmittedBindingStep.eta (abbreviation := abbreviation) (reader := reader)
          (parameters := parameters) (Child := Next) (names := target)
          (antecedent := HOL.rename rho _) (second := HOL.rename rho _))
  | variableBeta =>
      simpa only [HOL.rename, ExtDerivation.rename_instantiate] using
        (AdmittedBindingStep.variableBeta (abbreviation := abbreviation) (reader := reader)
          (parameters := parameters) (Child := Next) (names := target)
          (antecedent := HOL.rename rho _) (body := HOL.rename (Rename.lift rho) _)
          (argument := HOL.rename rho _))
  | constantAbstractionRenaming => exact .constantAbstractionRenaming
  | abstractionRenaming => exact .abstractionRenaming
  | @substitution antecedent result domain argument premise arg1 typeCode argumentCode arg5 name c1 c2 childWitness typeRead fresh argumentRead child same =>
      refine .substitution (argument := HOL.rename rho argument) typeRead ?_ ?_ (transform (by simp) (Rename.lift rho) (related.cons _ _) child) ?_
      · rwa [freshName_rename parameters bound _ rho source target related (bounded (.var _) (by simp))]
      · rw [readObjectWith_rename reader rho source target _ _
          (natural _ (expandEquivalence_varsBelow references abbreviation.reference bound _ (bounded _ (by simp)))),
          argumentRead]
        rfl
      · have renamed := congrArg (HOL.rename rho) same
        simpa only [instantiateNatural, ExtDerivation.rename_instantiate, HOL.rename] using renamed
  | beta fresh child same =>
      refine .beta ?_ (transform (by simp) (Rename.lift rho) (related.cons _ _) child) ?_
      · rwa [freshName_rename parameters bound _ rho source target related (bounded (.var _) (by simp))]
      · have renamed := congrArg (HOL.rename rho) same
        simpa only [instantiateNatural, ExtDerivation.rename_instantiate, HOL.rename] using renamed
  | @universalElimination antecedent result domain body argument premise arg1 arg2 argumentCode arg5 arg6 name c1 c2 substitutionWitness universalWitness universal fresh argumentRead substitutionAdmitted same =>
      refine .universalElimination (argument := HOL.rename rho argument) (transform (by simp) rho related universal) ?_ ?_
        (transform (by simp) (Rename.lift rho) (related.cons _ _) substitutionAdmitted) ?_
      · rwa [freshName_rename parameters bound _ rho source target related (bounded (.var _) (by simp))]
      · rw [readObjectWith_rename reader rho source target _ _
          (natural _ (expandEquivalence_varsBelow references abbreviation.reference bound _ (bounded _ (by simp)))),
          argumentRead]
        rfl
      · have renamed := congrArg (HOL.rename rho) same
        simpa only [instantiateNatural, ExtDerivation.rename_instantiate, HOL.rename] using renamed
  | @existentialIntroduction antecedent conclusion domain body argument premise arg1 arg2 argumentCode arg5 arg6 name c1 c2 substitutionWitness resultWitness fresh argumentRead result substitutionAdmitted same =>
      refine .existentialIntroduction (argument := HOL.rename rho argument) ?_ ?_ (transform (by simp) rho related result)
        (transform (by simp) (Rename.lift rho) (related.cons _ _) substitutionAdmitted) ?_
      · rwa [freshName_rename parameters bound _ rho source target related (bounded (.var _) (by simp))]
      · rw [readObjectWith_rename reader rho source target _ _
          (natural _ (expandEquivalence_varsBelow references abbreviation.reference bound _ (bounded _ (by simp)))),
          argumentRead]
        rfl
      · have renamed := congrArg (HOL.rename rho) same
        simpa only [instantiateNatural, ExtDerivation.rename_instantiate, HOL.rename] using renamed
  | existentialElimination existential fresh child =>
      refine .existentialElimination (transform (by simp) rho related existential) ?_ ?_
      · rwa [freshName_rename parameters bound _ rho source target related (bounded (.var _) (by simp))]
      · simpa only [HOL.rename, ExtDerivation.rename_weaken] using
          transform (by simp) (Rename.lift rho) (related.cons _ _) child

#print axioms AdmittedBindingStep.rename
end Mettapedia.Languages.MM0.HOLKernelBindingInterpretation

namespace Mettapedia.Languages.MM0.HOLKernelProofReadback
open Mettapedia.Logic Mettapedia.Logic.HOL
open Kernel HOLKernelSyntax HOLKernelTermReadback HOLKernelJudgmentReadback HOLKernelRuleReadback
open HOLKernelBindingInterpretation
universe u
variable {Const : Ty Unit → Type u} {gamma delta : Ctx Unit}
variable {terms : TermSignature} {definitions : Definition.Signature}
variable {references : HOLKernelSyntax.Symbol → Nat} {ids : SortIds}

section AdmissionUnderRenaming
open NamedElaboration (BinderNames)
variable {sorts : SortSignature} {signature : Signature sorts terms}
variable {theorems : TheoremSignature} {context : Context}

/-- Admission retained by a particular receipt in every well-formed reader frame
preserving its resolved variables and constants. This is stronger than successful
term readback; binding-rule eigenvariable checks need not survive arbitrary frame
extensions. The congruence compiler uses this property only for its input equalities. -/
def AdmissionUnderRenaming
    {gamma : Ctx Unit}
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (dictionary : Nat → Option (NamedElaboration.SomeConst Const)) (parameters : Nat)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (names : Names gamma) (witness : ProofWitness) (formula : Formula Const gamma) : Prop :=
  ∀ {delta : Ctx Unit} (rho : Rename Unit gamma delta) (target : Names delta),
    target.toList.Nodup → (∀ name ∈ target.toList, parameters ≤ name) →
    LookupPreserving dictionary rho names target →
    ∃ fuel, Nonempty (AdmittedProof abbreviation theorems context
      (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) parameters ruleAt bindingAt fuel
      target witness (HOL.rename rho formula))

theorem AdmissionUnderRenaming.at_identity
    {gamma : Ctx Unit}
    {abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids}
    {profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature}
    {dictionary : Nat → Option (NamedElaboration.SomeConst Const)} {parameters : Nat}
    {ruleAt : Nat → Option Rule} {bindingAt : Nat → Option HOLKernelBindingRules.Rule}
    {names : Names gamma} {witness : ProofWitness} {formula : Formula Const gamma}
    (stable : AdmissionUnderRenaming (context := context) abbreviation profile dictionary parameters ruleAt bindingAt names witness formula)
    (nodup : names.toList.Nodup) (above : ∀ name ∈ names.toList, parameters ≤ name) :
    ∃ fuel, Nonempty (AdmittedProof abbreviation theorems context
      (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) parameters ruleAt bindingAt fuel
      names witness formula) := by
  simpa only [rename_id] using stable Rename.id names nodup above (LookupPreserving.refl dictionary names)

theorem lookup_extension_can_capture_eigenvariable :
    LookupPreserving (Const := Const) (fun _ => none)
      (Rename.weaken (Γ := []) (σ := Ty.prop)) BinderNames.nil (BinderNames.cons 7 BinderNames.nil) ∧
      HOLKernelBindingInterpretation.freshName 7 (BinderNames.nil : Names []) 7 = true ∧
      HOLKernelBindingInterpretation.freshName 7 (BinderNames.cons 7 BinderNames.nil : Names [Ty.prop]) 7 = false := by
  refine ⟨LookupPreserving.weaken _ _ _ _ (by rfl) (by rfl), ?_⟩
  simp [HOLKernelBindingInterpretation.freshName]


#print axioms lookup_extension_can_capture_eigenvariable
end AdmissionUnderRenaming

def AdmittedChildren.rename
    {Child : ProofWitness → Formula Const gamma → Type u}
    {Next : ProofWitness → Formula Const delta → Type u}
    {children : List ProofWitness} {formulas : List (Formula Const gamma)}
    (rho : Rename Unit gamma delta)
    (admitted : AdmittedChildren Child children formulas)
    (transform : ∀ {child formula}, child ∈ children → Child child formula → Next child (HOL.rename rho formula)) :
    AdmittedChildren Next children (formulas.map (HOL.rename rho)) := by
  match admitted with
  | .nil => exact .nil
  | .cons head tail =>
      exact .cons (transform List.mem_cons_self head)
        (tail.rename rho (fun member proof => transform (List.mem_cons_of_mem _ member) proof))

/-- A native proof checked before unused slots were appended admits the same
source reading after a name-frame map agreeing on that original context.
The native witness, theorem policy and compiled theorem instances are retained. -/
theorem AdmittedProof.rename_of_prefix
    {abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions references ids}
    {theorems : TheoremSignature} {initial suffix : Context} {reader : TermReader Const}
    {parameters : Nat} {ruleAt : Nat → Option Rule} {bindingAt : Nat → Option HOLKernelBindingRules.Rule}
    (natural : ∀ {first second : Ctx Unit} (rho : Rename Unit first second)
      (source : Names first) (target : Names second), NamesRel initial.length rho source target →
      ∀ native : Preterm, Preterm.VarsBelow initial.length native →
        reader target native = (reader source native).map (Decoded.rename rho))
    {fuel : Nat} {source : Names gamma} {witness : ProofWitness} {formula : Formula Const gamma}
    (admitted : AdmittedProof abbreviation theorems (initial ++ suffix) reader parameters ruleAt bindingAt
      fuel source witness formula)
    (checked : ∃ native, ProofWitness.Checks terms definitions theorems initial [] witness native)
    (rho : Rename Unit gamma delta) (target : Names delta) (related : NamesRel initial.length rho source target) :
    Nonempty (AdmittedProof abbreviation theorems (initial ++ suffix) reader parameters ruleAt bindingAt
      fuel target witness (HOL.rename rho formula)) := by
  classical
  induction fuel generalizing gamma delta source witness formula with
  | zero => cases admitted
  | succ fuel ih =>
    cases admitted with
    | @formation witness native antecedent type term accepted judgment =>
        obtain ⟨oldNative, rechecked⟩ := checked
        have same : oldNative = native := Option.some.inj ((rechecked.weakenContext suffix).eval.symm.trans accepted)
        subst oldNative
        have bounded := rechecked.varsBelow (by simp)
        have renamed := readJudgmentWith_rename reader references initial.length rho source target
          (natural rho source target related) _
          (expandEquivalence_varsBelow references abbreviation.reference initial.length native bounded)
        rw [judgment] at renamed
        simp only [HOL.rename, ← Judgment.rename_formula rho antecedent]
        exact ⟨AdmittedStep.formation (antecedent := antecedent.rename rho) (term := HOL.rename rho term)
          accepted renamed⟩
    | @application index arguments children native accepted localRule sameConclusion childrenAdmitted =>
        obtain ⟨oldNative, rechecked⟩ := checked
        cases rechecked with
        | theoremApp declared instantiated childChecks =>
          have sameDecl := Option.some.inj (declared.symm.trans localRule.declared)
          subst sameDecl
          have sameInstance := (instantiated.weakenContext suffix).deterministic localRule.instantiated
          cases sameInstance
          let moved := localRule.rename initial.length rho target (natural rho source target related)
            instantiated.arguments_varsBelow instantiated.varsBelow.1 instantiated.varsBelow.2
          let movedChildren := childrenAdmitted.rename rho
            (fun member child => Classical.choice (ih child (childChecks.member member) rho target related))
          have conclusionEq : moved.operands.conclusion = HOL.rename rho localRule.operands.conclusion :=
            RuleArguments.rename_conclusion rho localRule.operands
          rw [← conclusionEq]
          exact ⟨AdmittedStep.application accepted moved sameConclusion (by
            simpa only [moved, AdmittedApplication.rename, RuleArguments.rename_premises] using movedChildren)⟩
    | @binding index arguments children native formula accepted bindingAdmitted =>
        obtain ⟨oldNative, rechecked⟩ := checked
        cases rechecked with
        | theoremApp declared instantiated childChecks =>
          have same := Option.some.inj
            (((ProofWitness.Checks.theoremApp declared instantiated childChecks).weakenContext suffix).eval.symm.trans accepted)
          have nativeBound : Preterm.VarsBelow initial.length native := same ▸ instantiated.varsBelow.2
          let moved : AdmittedBinding abbreviation theorems reader parameters bindingAt
              (fun {nextGamma} nextNames child childFormula =>
                AdmittedProof abbreviation theorems (initial ++ suffix) reader parameters ruleAt bindingAt
                  fuel nextNames child childFormula)
              target index arguments children native (HOL.rename rho formula) := {
            rule := bindingAdmitted.rule
            selected := bindingAdmitted.selected
            declared := bindingAdmitted.declared
            conclusion_read := by
              rw [readFormulaIn_rename abbreviation reader parameters initial.length rho source target
                (natural rho source target related) native nativeBound, bindingAdmitted.conclusion_read]
              rfl
            step := bindingAdmitted.step.rename initial.length rho target related
              (natural rho source target related) instantiated.arguments_varsBelow
              (fun member sigma related child => Classical.choice
                (ih child (childChecks.member member) sigma _ related)) }
          exact ⟨AdmittedStep.binding accepted moved⟩
    | @conversion conv child native sourceFormula formula accepted reading childAdmitted joinable =>
        obtain ⟨oldNative, rechecked⟩ := checked
        cases rechecked with
        | conversion converted childChecks =>
          have same := Option.some.inj
            (((ProofWitness.Checks.conversion converted childChecks).weakenContext suffix).eval.symm.trans accepted)
          have nativeBound : Preterm.VarsBelow initial.length native := same ▸ converted.typed.2.varsBelow
          have renamedRead := readFormulaIn_rename abbreviation reader parameters initial.length rho source target
            (natural rho source target related) native nativeBound
          rw [reading] at renamedRead
          obtain ⟨movedChild⟩ := ih childAdmitted ⟨_, childChecks⟩ rho target related
          have movedJoin : ConversionTiers.Joinable (HOL.rename rho sourceFormula) (HOL.rename rho formula) := by
            obtain ⟨meet, ⟨left⟩, ⟨right⟩⟩ := joinable
            refine ⟨HOL.rename rho meet, ?_, ?_⟩
            · simpa only [subst_ofRename] using Nonempty.intro (left.subst (Subst.ofRename rho))
            · simpa only [subst_ofRename] using Nonempty.intro (right.subst (Subst.ofRename rho))
          exact ⟨AdmittedStep.conversion accepted renamedRead movedChild movedJoin⟩

/-- The maintained logical reader instantiates the frame transport directly.
A fresh name beyond the checked context weakens the complete source proof. -/
theorem AdmittedProof.logical_weaken_of_prefix
    {sorts : SortSignature} {theorems : TheoremSignature} {signature : Signature sorts terms}
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    {abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids}
    (constants : Nat → Option (NamedElaboration.SomeConst Const))
    {initial suffix : Context} {parameters : Nat}
    {ruleAt : Nat → Option Rule} {bindingAt : Nat → Option HOLKernelBindingRules.Rule}
    {fuel : Nat} {names : Names gamma} {witness : ProofWitness} {formula : Formula Const gamma}
    (admitted : AdmittedProof abbreviation theorems (initial ++ suffix)
      (HOLKernelLogicalFunctionReadback.reader profile constants parameters)
      parameters ruleAt bindingAt fuel names witness formula)
    (checked : ∃ native, ProofWitness.Checks terms definitions theorems initial [] witness native)
    (domain : Ty Unit) (fresh : Nat) (beyond : initial.length ≤ fresh) :
    Nonempty (AdmittedProof abbreviation theorems (initial ++ suffix)
      (HOLKernelLogicalFunctionReadback.reader profile constants parameters)
      parameters ruleAt bindingAt fuel (NamedElaboration.BinderNames.cons (type := domain) fresh names)
      witness (weaken (σ := domain) formula)) :=
  admitted.rename_of_prefix
    (fun rho source target related native bounded =>
      logical_reader_rename profile constants parameters initial.length source target rho related native bounded)
    checked (fun {_} index => Var.vs index) _ (NamesRel.weaken names domain fresh beyond)

#print axioms AdmittedProof.logical_weaken_of_prefix

#print axioms AdmittedProof.rename_of_prefix
theorem AdmittedProof.rename_of_varsBelow
    {abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions references ids}
    {theorems : TheoremSignature} {initial suffix : Context} {reader : TermReader Const}
    {parameters : Nat} {ruleAt : Nat → Option Rule} {bindingAt : Nat → Option HOLKernelBindingRules.Rule}
    (natural : ∀ {first second : Ctx Unit} (rho : Rename Unit first second)
      (source : Names first) (target : Names second), NamesRel initial.length rho source target →
      ∀ native : Preterm, Preterm.VarsBelow initial.length native →
        reader target native = (reader source native).map (Decoded.rename rho))
    {fuel : Nat} {source : Names gamma} {witness : ProofWitness} {formula : Formula Const gamma}
    (admitted : AdmittedProof abbreviation theorems (initial ++ suffix) reader parameters ruleAt bindingAt
      fuel source witness formula)
    (bounded : witness.VarsBelow initial.length)
    (rho : Rename Unit gamma delta) (target : Names delta) (related : NamesRel initial.length rho source target) :
    Nonempty (AdmittedProof abbreviation theorems (initial ++ suffix) reader parameters ruleAt bindingAt
      fuel target witness (HOL.rename rho formula)) := by
  obtain ⟨native, accepted⟩ := admitted.accepted
  have original := (ProofWitness.proof_in_prefix_iff terms definitions theorems initial suffix [] witness native).mpr
    ⟨accepted, bounded⟩
  exact admitted.rename_of_prefix natural
    ⟨native, (ProofWitness.proof_eq_some_iff _ _ _ _ _ _ _).mp original⟩ rho target related

#print axioms AdmittedProof.rename_of_varsBelow
section NativeContextWeakening
open NamedElaboration (BinderNames)
variable {sorts : SortSignature} {theorems : TheoremSignature}
variable {signature : Signature sorts terms} {context : Context}

theorem AdmittedProof.logical_weaken_of_varsBelow
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (constants : Nat → Option (NamedElaboration.SomeConst Const)) (parameters : Nat)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    {fuel : Nat} {names : Names gamma} {witness : ProofWitness} {formula : Formula Const gamma}
    (admitted : AdmittedProof abbreviation theorems context
      (HOLKernelLogicalFunctionReadback.reader profile constants parameters)
      parameters ruleAt bindingAt fuel names witness formula)
    (bound : Nat) (within : bound ≤ context.length) (bounded : witness.VarsBelow bound)
    (domain : Ty Unit) (fresh : Nat) (later : bound ≤ fresh) :
    Nonempty (AdmittedProof abbreviation theorems context
      (HOLKernelLogicalFunctionReadback.reader profile constants parameters)
      parameters ruleAt bindingAt fuel (BinderNames.cons (type := domain) fresh names) witness (weaken (σ := domain) formula)) := by
  let initial := context.take bound
  let suffix := context.drop bound
  have size : initial.length = bound := by simp [initial, List.length_take, Nat.min_eq_left within]
  have joined : initial ++ suffix = context := List.take_append_drop bound context
  have original : AdmittedProof abbreviation theorems (initial ++ suffix)
      (HOLKernelLogicalFunctionReadback.reader profile constants parameters)
      parameters ruleAt bindingAt fuel names witness formula := by rw [joined]; exact admitted
  have lifted := original.rename_of_varsBelow
    (fun rho source target related native nativeBound =>
      logical_reader_rename profile constants parameters initial.length source target rho related native nativeBound)
    (by rw [size]; exact bounded) (fun {_} index => Var.vs (σ := domain) index)
    (BinderNames.cons fresh names) (NamesRel.weaken names domain fresh (by rw [size]; exact later))
  rw [joined] at lifted
  exact lifted

#print axioms AdmittedProof.logical_weaken_of_varsBelow
end NativeContextWeakening
end Mettapedia.Languages.MM0.HOLKernelProofReadback
