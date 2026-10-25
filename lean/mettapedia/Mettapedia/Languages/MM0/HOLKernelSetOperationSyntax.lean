import Mettapedia.Languages.MM0.HOLKernelTypingProofs
import Mettapedia.Languages.MM0.HOLKernelAssumptions
import Mettapedia.Languages.MM0.HOLKernelTermAssignments
import Mettapedia.Logic.HOL.SetOperationSignature
import Mettapedia.Logic.HOL.Syntax.Closed

/-!
# Native syntax and formation for the six material operations

A regular type parameter and six distinct regular term parameters encode the
common higher-order signature. Their object-level typings form the explicit
formation antecedent. Source formulas remain ordered logical assumptions.
The encoding uses a separate bank of bound names for typed object binders.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.MM0.HOLKernelSetOperationInterpretation
open Mettapedia.Logic.HOL
open Embedding.ZFSetHenkinInterpretation (Symbol set predicate mapping)
open Kernel HOLKernelSyntax HOLKernelJudgment HOLKernelTermAssignments
open HOLKernelTypingRules (typed)
open HOLKernelStructuralRules (CheckedProof)
variable {sorts : SortSignature} {terms : TermSignature} {definitions : Definition.Signature}
variable {theorems : TheoremSignature}

abbrev Formula := ClosedFormula Symbol

def initialContext (ids : SortIds) : Context :=
  [.regular ids.type ∅, .regular ids.object ∅, .regular ids.object ∅,
   .regular ids.object ∅, .regular ids.object ∅, .regular ids.object ∅, .regular ids.object ∅]

def typeCode (_ : Unit) : Preterm := .var 0

def symbolIndex : {type : Ty Unit} → Symbol type → Nat
  | _, .member => 1
  | _, .empty => 2
  | _, .union => 3
  | _, .power => 4
  | _, .separate => 5
  | _, .replace => 6

def symbolCode {type : Ty Unit} (symbol : Symbol type) : Preterm := .var (symbolIndex symbol)

theorem symbolIndex_injective {firstType secondType : Ty Unit}
    (first : Symbol firstType) (second : Symbol secondType)
    (same : symbolIndex first = symbolIndex second) : HEq first second := by
  cases first <;> cases second <;> simp_all [symbolIndex]

theorem union_power_distinct : symbolCode Symbol.union ≠ symbolCode Symbol.power := by decide

theorem initialContext_formed (signature : Signature sorts terms) :
    Context.WellFormed sorts (initialContext signature.ids) := by
  apply (Context.check_iff _ _).mp
  simp [initialContext, Context.check, Context.checkFrom, Context.checkBinder,
    signature.typeDeclared, signature.objectDeclared]

theorem typeCode_sorted (signature : Signature sorts terms) (index : Unit) :
    Preterm.HasType terms (initialContext signature.ids) (typeCode index) [] signature.ids.type :=
  .var (binder := .regular signature.ids.type ∅) rfl

theorem symbolCode_sorted (signature : Signature sorts terms) {type : Ty Unit} (symbol : Symbol type) :
    Preterm.HasType terms (initialContext signature.ids) (symbolCode symbol) [] signature.ids.object := by
  cases symbol <;> exact .var (binder := .regular signature.ids.object ∅) rfl

def symbols : List (Σ type : Ty Unit, Symbol type) :=
  [⟨_, .member⟩, ⟨_, .empty⟩, ⟨_, .union⟩, ⟨_, .power⟩, ⟨_, .separate⟩, ⟨_, .replace⟩]

def typingAssumptions (references : HOLKernelSyntax.Symbol → Nat) : List Preterm :=
  symbols.map (fun entry => hasType references (symbolCode entry.2) (encodeType references typeCode entry.1))

def position {type : Ty Unit} : (symbol : Symbol type) → Fin symbols.length
  | .member => ⟨0, by decide⟩
  | .empty => ⟨1, by decide⟩
  | .union => ⟨2, by decide⟩
  | .power => ⟨3, by decide⟩
  | .separate => ⟨4, by decide⟩
  | .replace => ⟨5, by decide⟩

theorem typingAssumption_at (references : HOLKernelSyntax.Symbol → Nat) {type : Ty Unit} (symbol : Symbol type) :
    (typingAssumptions references).get ⟨(position symbol).val, by simp [typingAssumptions]⟩ =
      hasType references (symbolCode symbol) (encodeType references typeCode type) := by
  cases symbol <;> rfl

theorem typingAssumptions_sorted (signature : Signature sorts terms) :
    ∀ expression ∈ typingAssumptions signature.symbol,
      Preterm.HasType terms (initialContext signature.ids) expression [] signature.ids.wff := by
  intro expression member
  obtain ⟨entry, _, rfl⟩ := List.mem_map.mp member
  exact hasType_sorted signature _ (symbolCode_sorted signature entry.2)
    (encodeType_sorted signature _ typeCode (typeCode_sorted signature) entry.1)

def baseAntecedent (references : HOLKernelSyntax.Symbol → Nat) : Preterm :=
  holds references (applySymbol references .truth [])

def formation (references : HOLKernelSyntax.Symbol → Nat) : Preterm :=
  HOLKernelAssumptions.antecedent references (baseAntecedent references) (typingAssumptions references)

theorem formation_sorted (signature : Signature sorts terms) :
    Preterm.HasType terms (initialContext signature.ids) (formation signature.symbol) [] signature.ids.wff :=
  HOLKernelAssumptions.antecedent_sorted signature _ (holds_sorted signature _ (signature.application _ .truth [] .nil))
    _ (typingAssumptions_sorted signature)

def constantTyping (signature : Signature sorts terms)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    {type : Ty Unit} (symbol : Symbol type) :
    CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := initialContext signature.ids) (hypotheses := [])
      (typed signature.symbol (formation signature.symbol) (symbolCode symbol) (encodeType signature.symbol typeCode type)) := by
  let occurrence : Fin (typingAssumptions signature.symbol).length := ⟨(position symbol).val, by simp [typingAssumptions]⟩
  have proof := HOLKernelAssumptions.hypothesis (definitions := definitions) (hypotheses := []) signature structural
    (baseAntecedent signature.symbol) (holds_sorted signature _ (signature.application _ .truth [] .nil))
    (typingAssumptions signature.symbol) (typingAssumptions_sorted signature) occurrence
  change CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
    (context := initialContext signature.ids) (hypotheses := [])
    (entails signature.symbol (formation signature.symbol) ((typingAssumptions signature.symbol).get occurrence)) at proof
  rw [typingAssumption_at] at proof
  exact proof

def noAssignment : Assignment ([] : Ctx Unit) := fun index => nomatch index

def binderName (depth : Nat) : Nat := symbols.length + 1 + depth


def term (references : HOLKernelSyntax.Symbol → Nat) {type : Ty Unit} (source : ClosedTerm Symbol type) : Preterm :=
  encodeWithAssignment references typeCode (fun {_} symbol => symbolCode symbol)
    binderName noAssignment 0 source

/-- The actual context has seven initial entries, independently of sort IDs. -/
theorem initialContext_length (ids : SortIds) : (initialContext ids).length = 7 := rfl

def statement (references : HOLKernelSyntax.Symbol → Nat) (assumptions : List Formula) (conclusion : Formula) : Preterm :=
  entails references (HOLKernelAssumptions.antecedent references (formation references)
    (assumptions.map (fun source => holds references (term references source)))) (holds references (term references conclusion))

end Mettapedia.Languages.MM0.HOLKernelSetOperationInterpretation
