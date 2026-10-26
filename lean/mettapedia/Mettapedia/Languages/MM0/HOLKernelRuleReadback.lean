import Mettapedia.Languages.MM0.HOLKernelTermAssignments
import Mettapedia.Languages.MM0.HOLKernelInferenceInterpretation
import Mettapedia.Languages.MM0.HOLKernelBooleanEquality
import Mettapedia.Logic.HOL.Syntax.DecidableEq

/-!
# Reading licensed nonbinding MM0 rule applications

An application is read from its actual theorem-table entry and simultaneous
substitution. Its interpreted ordered premises and conclusion must agree
with a constructed source proof. The Boolean-equivalence reading requires
the maintained abbreviation's actual declaration and stored definition.
Typing rules retain term reconstruction before their discharged formation
claim receives the logical reading of truth.

The result is a local proof interpretation. It composes with supplied child
proof readings; it does not infer those proofs from statement syntax.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.HOLKernelRuleReadback

open Mettapedia.Logic.HOL
open Kernel HOLKernelSyntax HOLKernelTermReadback HOLKernelJudgmentReadback
open HOLKernelInferenceInterpretation
open NamedElaboration (SomeConst)

universe u
variable {Const : Ty Unit → Type u} {gamma : Ctx Unit}

inductive Rule where
  | structural (rule : HOLKernelStructuralRules.Rule)
  | typing (rule : HOLKernelTypingRules.Rule)
  | inference (rule : HOLKernelInferenceRules.Rule)
  deriving DecidableEq, Repr

def Rule.declaration (references : HOLKernelSyntax.Symbol → Nat)
    (ids : SortIds) (equivalenceReference : Nat) : Rule → TheoremDecl
  | .structural rule => rule.declaration references ids.wff
  | .typing rule => rule.declaration references ids
  | .inference rule => rule.declaration references ids equivalenceReference

/-- Expand the separately licensed Boolean-equality abbreviation. This is
syntax reading under its supplied definition, rather than an additional
object-theory equality axiom. -/
def expandEquivalence (references : HOLKernelSyntax.Symbol → Nat)
    (equivalenceReference : Nat) : Preterm → Preterm
  | .app (.app (.term index) first) second =>
      if index = equivalenceReference then
        HOLKernelBooleanEquality.expanded references
          (expandEquivalence references equivalenceReference first)
          (expandEquivalence references equivalenceReference second)
      else .app (.app (.term index) (expandEquivalence references equivalenceReference first))
        (expandEquivalence references equivalenceReference second)
  | .app function argument => .app
      (expandEquivalence references equivalenceReference function)
      (expandEquivalence references equivalenceReference argument)
  | .var index => .var index
  | .term index => .term index
termination_by native => sizeOf native

section EncodedFixedPoints
open HOLKernelTermAssignments
universe v w
variable {Base : Type v} {Family : Ty Base → Type w}

theorem expandEquivalence_encodeType_of_fixed (references : HOLKernelSyntax.Symbol → Nat)
    (equivalenceReference : Nat) (distinct : ∀ symbol, references symbol ≠ equivalenceReference)
    (base : Base → Preterm) (baseFixed : ∀ name, expandEquivalence references equivalenceReference (base name) = base name)
    (type : Ty Base) :
    expandEquivalence references equivalenceReference (encodeType references base type) = encodeType references base type := by
  induction type <;> simp_all [encodeType, applySymbol, Preterm.applyArgs, expandEquivalence]

theorem expandEquivalence_encodeWithAssignment_of_fixed (references : HOLKernelSyntax.Symbol → Nat)
    (equivalenceReference : Nat) (distinct : ∀ symbol, references symbol ≠ equivalenceReference)
    (base : Base → Preterm) (constant : ∀ {type}, Family type → Preterm) (binders : Nat → Nat)
    (baseFixed : ∀ name, expandEquivalence references equivalenceReference (base name) = base name)
    (constantFixed : ∀ {type} (symbol : Family type), expandEquivalence references equivalenceReference (constant symbol) = constant symbol)
    {gamma : Ctx Base} {type : Ty Base} (source : Term Family gamma type) :
    ∀ (assignment : Assignment gamma) (depth : Nat),
      (∀ {type} (index : Var gamma type), expandEquivalence references equivalenceReference (assignment index) = assignment index) →
      expandEquivalence references equivalenceReference (encodeWithAssignment references base constant binders assignment depth source) =
        encodeWithAssignment references base constant binders assignment depth source := by
  induction source with
  | @lam domain gamma result body ih | @all domain gamma body ih | @ex domain gamma body ih =>
      intro assignment depth fixed
      have extendedFixed : ∀ {type} (index : Var (domain :: gamma) type),
          expandEquivalence references equivalenceReference
            (Assignment.extend (.var (binders depth)) assignment index) =
              Assignment.extend (.var (binders depth)) assignment index := by
        intro type index
        cases index with
        | vz => simp [Assignment.extend, expandEquivalence]
        | vs index => exact fixed index
      simp [encodeWithAssignment, applySymbol, Preterm.applyArgs, expandEquivalence, distinct,
        expandEquivalence_encodeType_of_fixed references equivalenceReference distinct base baseFixed,
        ih _ _ extendedFixed]
  | var index | const symbol | top | bot | app first second ihFirst ihSecond
  | and first second ihFirst ihSecond | or first second ihFirst ihSecond | imp first second ihFirst ihSecond
  | not body ih | eq first second ihFirst ihSecond =>
      intros
      simp_all [encodeWithAssignment, applySymbol, Preterm.applyArgs, expandEquivalence,
        expandEquivalence_encodeType_of_fixed references equivalenceReference distinct base baseFixed]

theorem expandEquivalence_encodeTerm_of_fixed (references : HOLKernelSyntax.Symbol → Nat)
    (equivalenceReference : Nat) (distinct : ∀ symbol, references symbol ≠ equivalenceReference)
    (base : Base → Preterm) (constant : ∀ {type}, Family type → Preterm) (binders : Nat → Nat)
    (baseFixed : ∀ name, expandEquivalence references equivalenceReference (base name) = base name)
    (constantFixed : ∀ {type} (symbol : Family type),
      expandEquivalence references equivalenceReference (constant symbol) = constant symbol)
    {gamma : Ctx Base} {type : Ty Base} (source : Term Family gamma type) :
    ∀ (positions : Positions gamma) (depth : Nat),
      expandEquivalence references equivalenceReference (encodeTerm references base constant binders positions depth source) =
        encodeTerm references base constant binders positions depth source := by
  intro positions depth
  have fixed := expandEquivalence_encodeWithAssignment_of_fixed references equivalenceReference distinct base constant binders
    baseFixed constantFixed source (fun index => .var (positions index)) depth
    (fun _ => by simp [expandEquivalence])
  simpa only [encode_positions] using fixed

end EncodedFixedPoints

variable {terms : TermSignature} {definitions : Definition.Signature}
variable {references : HOLKernelSyntax.Symbol → Nat} {ids : SortIds}

def readFormulaIn (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions references ids)
    (reader : TermReader Const) (_parameters : Nat) (names : Names gamma)
    (native : Preterm) : Option (Formula Const gamma) :=
  (readJudgmentWith reader references names
    (expandEquivalence references abbreviation.reference native)).map Judgment.formula

/-- Typed formation data, without a source proof. -/
structure TypingArguments (Const : Ty Unit → Type u) (gamma : Ctx Unit) where
  premises : List (Formula Const gamma)
  antecedent : Judgment Const gamma
  type : Ty Unit
  term : Term Const gamma type

/-- Source operands for a selected native schema. No constructor contains
HOL proof syntax or an assertion of source derivability. -/
inductive RuleArguments (Const : Ty Unit → Type u) (gamma : Ctx Unit) : Rule → Type u where
  | structural {rule : HOLKernelStructuralRules.Rule}
      (arguments : HOLKernelRuleInstances.StructuralArguments Const gamma rule) :
      RuleArguments Const gamma (.structural rule)
  | inference {rule : HOLKernelInferenceRules.Rule}
      (arguments : HOLKernelRuleInstances.InferenceArguments Const gamma rule) :
      RuleArguments Const gamma (.inference rule)
  | typing (rule : HOLKernelTypingRules.Rule) (arguments : TypingArguments Const gamma) :
      RuleArguments Const gamma (.typing rule)

def RuleArguments.premises {rule : Rule} : RuleArguments Const gamma rule → List (Formula Const gamma)
  | .structural arguments => arguments.premises
  | .inference arguments => arguments.premises
  | .typing _ arguments => arguments.premises

def RuleArguments.conclusion {rule : Rule} : RuleArguments Const gamma rule → Formula Const gamma
  | .structural arguments => arguments.conclusion
  | .inference arguments => arguments.conclusion
  | .typing _ arguments => .imp arguments.antecedent.formula .top

def readTypingArguments
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions references ids)
    (reader : TermReader Const) (parameters : Nat) (names : Names gamma)
    (native : TheoremInstance) : Option (TypingArguments Const gamma) := do
  let premises ← native.hypotheses.mapM (readFormulaIn abbreviation reader parameters names)
  let .consequence antecedent (.typing term) ← readJudgmentWith reader references names
    (expandEquivalence references abbreviation.reference native.conclusion) | none
  pure ⟨premises, antecedent, _, term⟩

def readArguments
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions references ids)
    (reader : TermReader Const) (parameters : Nat) (names : Names gamma)
    (rule : Rule) (arguments : List Preterm) (native : TheoremInstance) :
    Option (RuleArguments Const gamma rule) :=
  match rule with
  | .typing rule => (readTypingArguments abbreviation reader parameters names native).map (.typing rule)
  | .structural _ =>
      (HOLKernelRuleInstances.readStructuralArguments reader references names _
        (arguments.map (expandEquivalence references abbreviation.reference))).map .structural
  | .inference _ =>
      (HOLKernelRuleInstances.readInferenceArguments reader references names _
        (arguments.map (expandEquivalence references abbreviation.reference))).map .inference

/-- A total proof construction for every typed local schema instance. -/
def RuleArguments.interpret {rule : Rule} : RuleArguments Const gamma rule → InterpretedRule Const gamma
  | .structural arguments => interpretStructural arguments
  | .inference arguments => interpretInference arguments
  | .typing _ arguments => ⟨arguments.premises, .imp arguments.antecedent.formula .top, .impI .topI⟩

@[simp] theorem RuleArguments.interpret_premises {rule : Rule} (arguments : RuleArguments Const gamma rule) :
    arguments.interpret.premises = arguments.premises := by cases arguments <;> rfl

@[simp] theorem RuleArguments.interpret_conclusion {rule : Rule} (arguments : RuleArguments Const gamma rule) :
    arguments.interpret.conclusion = arguments.conclusion := by cases arguments <;> rfl

structure InterpretedInstance
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions references ids)
    (reader : TermReader Const) (parameters : Nat) (names : Names gamma)
    (native : TheoremInstance) where
  source : InterpretedRule Const gamma
  premises_read : native.hypotheses.mapM
    (readFormulaIn abbreviation reader parameters names) = some source.premises
  conclusion_read : readFormulaIn abbreviation reader parameters names native.conclusion =
    some source.conclusion

variable [∀ type, DecidableEq (Const type)]

def matchInstance
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions references ids)
    (reader : TermReader Const) (parameters : Nat) (names : Names gamma)
    (native : TheoremInstance) (candidate : InterpretedRule Const gamma) :
    Option (InterpretedInstance abbreviation reader parameters names native) :=
  if premises : native.hypotheses.mapM
      (readFormulaIn abbreviation reader parameters names) = some candidate.premises then
    if conclusion : readFormulaIn abbreviation reader parameters names native.conclusion =
        some candidate.conclusion then
      some ⟨candidate, premises, conclusion⟩
    else none
  else none

def readTypingInstance
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions references ids)
    (reader : TermReader Const) (parameters : Nat) (names : Names gamma)
    (native : TheoremInstance) :
    Option (InterpretedInstance abbreviation reader parameters names native) := do
  let arguments ← readTypingArguments abbreviation reader parameters names native
  matchInstance abbreviation reader parameters names native
    ⟨arguments.premises, .imp arguments.antecedent.formula .top, .impI .topI⟩

def readInstance
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions references ids)
    (reader : TermReader Const) (parameters : Nat) (names : Names gamma)
    (rule : Rule) (arguments : List Preterm) (native : TheoremInstance) :
    Option (InterpretedInstance abbreviation reader parameters names native) := do
  let operands ← readArguments abbreviation reader parameters names rule arguments native
  matchInstance abbreviation reader parameters names native operands.interpret

structure InterpretedApplication
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions references ids)
    (theorems : TheoremSignature) (context : Context)
    (reader : TermReader Const) (parameters : Nat) (names : Names gamma)
    (index : Nat) (arguments : List Preterm) where
  rule : Rule
  native : TheoremInstance
  declared : theorems index = some (rule.declaration references ids abbreviation.reference)
  instantiated : TheoremDecl.Instantiates terms context
    (rule.declaration references ids abbreviation.reference) arguments native
  interpretation : InterpretedInstance abbreviation reader parameters names native

def readApplication
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions references ids)
    (theorems : TheoremSignature) (context : Context)
    (reader : TermReader Const) (parameters : Nat) (names : Names gamma)
    (ruleAt : Nat → Option Rule) (index : Nat) (arguments : List Preterm) :
    Option (InterpretedApplication abbreviation theorems context reader parameters names index arguments) :=
  match ruleAt index with
  | none => none
  | some rule =>
      if declared : theorems index = some (rule.declaration references ids abbreviation.reference) then
        match instantiated : (rule.declaration references ids abbreviation.reference).instantiate? terms context arguments with
        | none => none
        | some native => do
            let interpretation ← readInstance abbreviation reader parameters names rule arguments native
            pure ⟨rule, native, declared,
              (TheoremDecl.instantiate_eq_some_iff _ _ _ _ _).mp instantiated, interpretation⟩
      else none

/-- Admission of a local native application refers only to its actual
header, substitution, typed operands and exact sequent readings. It contains
no source proof and does not refer to successful proof reconstruction. -/
structure AdmittedApplication
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions references ids)
    (theorems : TheoremSignature) (context : Context)
    (reader : TermReader Const) (parameters : Nat) (names : Names gamma)
    (ruleAt : Nat → Option Rule) (index : Nat) (arguments : List Preterm) where
  rule : Rule
  selected : ruleAt index = some rule
  native : TheoremInstance
  declared : theorems index = some (rule.declaration references ids abbreviation.reference)
  instantiated : TheoremDecl.Instantiates terms context
    (rule.declaration references ids abbreviation.reference) arguments native
  operands : RuleArguments Const gamma rule
  operands_read : readArguments abbreviation reader parameters names rule arguments native = some operands
  premises_read : native.hypotheses.mapM (readFormulaIn abbreviation reader parameters names) =
    some operands.premises
  conclusion_read : readFormulaIn abbreviation reader parameters names native.conclusion =
    some operands.conclusion

/-- Construct the source rule proof from the proof-free local admission data. -/
def AdmittedApplication.interpret
    {abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions references ids}
    {theorems : TheoremSignature} {context : Context}
    {reader : TermReader Const} {parameters : Nat} {names : Names gamma}
    {ruleAt : Nat → Option Rule} {index : Nat} {arguments : List Preterm}
    (admitted : AdmittedApplication abbreviation theorems context reader parameters names ruleAt index arguments) :
    InterpretedApplication abbreviation theorems context reader parameters names index arguments :=
  ⟨admitted.rule, admitted.native, admitted.declared, admitted.instantiated,
    ⟨admitted.operands.interpret,
      by simpa only [RuleArguments.interpret_premises] using admitted.premises_read,
      by simpa only [RuleArguments.interpret_conclusion] using admitted.conclusion_read⟩⟩

theorem readApplication_eq_of_admitted
    {abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions references ids}
    {theorems : TheoremSignature} {context : Context}
    {reader : TermReader Const} {parameters : Nat} {names : Names gamma}
    {ruleAt : Nat → Option Rule} {index : Nat} {arguments : List Preterm}
    (admitted : AdmittedApplication abbreviation theorems context reader parameters names ruleAt index arguments) :
    readApplication abbreviation theorems context reader parameters names ruleAt index arguments =
      some admitted.interpret := by
  simp only [readApplication, admitted.selected, admitted.declared, dite_true]
  split
  next refused =>
    have accepted := admitted.instantiated.eval
    rw [refused] at accepted
    contradiction
  next native computed =>
    have same : native = admitted.native := Option.some.inj (computed.symm.trans admitted.instantiated.eval)
    subst native
    simp only [readInstance, admitted.operands_read, Option.bind_eq_bind, Option.bind_some]
    simp only [matchInstance, RuleArguments.interpret_premises, RuleArguments.interpret_conclusion,
      admitted.premises_read, admitted.conclusion_read]
    rfl

/-- Compose an actual interpreted native application with source proofs at
its ordered premise occurrences. The declaration and substitution evidence
remain in `application`; neither is supplied as a source proof. -/
def InterpretedApplication.apply
    {abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions references ids}
    {theorems : TheoremSignature} {context : Context}
    {reader : TermReader Const} {parameters : Nat} {names : Names gamma}
    {index : Nat} {arguments : List Preterm}
    (application : InterpretedApplication abbreviation theorems context reader parameters names index arguments)
    {assumptions : List (Formula Const gamma)}
    (children : ProofSyntax.HypothesisSubstitution application.interpretation.source.premises assumptions) :
    ProofSyntax Const assumptions application.interpretation.source.conclusion :=
  application.interpretation.source.apply children

#print axioms readApplication
#print axioms InterpretedApplication.apply

end Mettapedia.Languages.MM0.HOLKernelRuleReadback
