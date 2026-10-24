import Mettapedia.Languages.MM0.HOLKernelProofCompilation
import Mettapedia.Logic.HOL.Soundness
import Mettapedia.Logic.HOL.Semantics.ModelProperties

/-!
# Constant identification obstructs HOL source reflection

Two Boolean source constants have distinct values in a full-domain HOL model.
Their equality is therefore not derivable in the retained source calculus.
A typed native representation may nevertheless map both to maintained HOL
truth. Native reflexivity then checks at the encoded equality.

Formation and forward proof preservation alone cannot yield a converse for
arbitrary accepted native proofs of encoded statements. Source reflection
needs a more restricted representation and an admitted certificate image.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.MM0.HOLKernelEncodingReflection
open Mettapedia.Logic.HOL
open Kernel HOLKernelSyntax HOLKernelJudgment HOLKernelTermAssignments
open HOLKernelStructuralRules (CheckedProof)

inductive Constant : Ty Unit → Type where
  | first : Constant .prop
  | second : Constant .prop

def source : ClosedFormula Constant := .eq (.const .first) (.const .second)
noncomputable def model : HenkinModel.{0, 0, 0} Unit Constant :=
  HenkinModel.standard (fun _ => ULift.{1} Unit)
    (fun {_} symbol => match symbol with
      | .first => .up True
      | .second => .up False)

theorem source_invalid : ¬ model.models source := by
  change ¬ (True ↔ False)
  exact fun equal => equal.mp trivial

theorem source_not_derivable : IsEmpty (ProofSyntax Constant [] source) := by
  refine ⟨fun proof => ?_⟩
  exact source_invalid (Soundness.extDerivation_sound (M := model) proof.erase
    (model.functionsRespectEqv_of_fullDomains (HenkinModel.fullDomains_standard _ _))
    (fun index => nomatch index) (by intro formula member; simp at member))

def collapsed (references : Symbol → Nat) : ∀ {type}, Constant type → Preterm
  | _, .first | _, .second => applySymbol references .truth []

def encodedSource (references : Symbol → Nat) : Preterm :=
  encodeWithAssignment references (fun _ : Unit => HOLKernelTypingRules.boolType references)
    (collapsed references) id (fun {type} (index : Var ([] : Ctx Unit) type) => nomatch index) 0 source

theorem source_representation_collapses (references : Symbol → Nat) :
    encodedSource references = HOLKernelInferenceRules.equality references
      (HOLKernelTypingRules.boolType references) (applySymbol references .truth []) (applySymbol references .truth []) := rfl

variable {sorts : SortSignature} {terms : TermSignature} {definitions : Definition.Signature}
variable {theorems : TheoremSignature} {context : Context} {hypotheses : List Preterm} {equivalenceReference : Nat}

theorem collapsed_sorted (signature : Signature sorts terms) {type : Ty Unit} (symbol : Constant type) :
    Preterm.HasType terms context (collapsed signature.symbol symbol) [] signature.ids.object := by
  cases symbol <;> exact signature.application context .truth [] .nil

def collapsed_typed (signature : Signature sorts terms)
    (typing : HOLKernelTypingRules.Rules theorems signature.symbol signature.ids)
    (antecedent : Preterm) (sorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    {type : Ty Unit} (symbol : Constant type) :
    CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems) (context := context) (hypotheses := hypotheses)
      (HOLKernelTypingRules.typed signature.symbol antecedent (collapsed signature.symbol symbol)
        (encodeType signature.symbol (fun _ : Unit => HOLKernelTypingRules.boolType signature.symbol) type)) := by
  cases symbol <;> exact HOLKernelTypingProofs.truthTyping signature typing antecedent sorted

def acceptedCollapsedSource (signature : Signature sorts terms)
    (typing : HOLKernelTypingRules.Rules theorems signature.symbol signature.ids)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids equivalenceReference)
    (antecedent : Preterm) (sorted : Preterm.HasType terms context antecedent [] signature.ids.wff) :
    CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems) (context := context) (hypotheses := hypotheses)
      (entails signature.symbol antecedent (holds signature.symbol (encodedSource signature.symbol))) :=
  HOLKernelInferenceProofs.Native.reflexivity signature rules antecedent (HOLKernelTypingRules.boolType signature.symbol)
    (applySymbol signature.symbol .truth []) sorted (signature.application context .bool [] .nil)
    (signature.application context .truth [] .nil) (HOLKernelTypingProofs.truthTyping signature typing antecedent sorted)

theorem acceptedCollapsedSource_checks (signature : Signature sorts terms)
    (typing : HOLKernelTypingRules.Rules theorems signature.symbol signature.ids)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids equivalenceReference)
    (antecedent : Preterm) (sorted : Preterm.HasType terms context antecedent [] signature.ids.wff) :
    (acceptedCollapsedSource (definitions := definitions) (hypotheses := hypotheses) signature typing rules antecedent sorted).val.check
      terms definitions theorems context hypotheses
      (entails signature.symbol antecedent (holds signature.symbol (encodedSource signature.symbol))) = true ∧
    IsEmpty (ProofSyntax Constant [] source) :=
  ⟨(ProofWitness.check_iff _ _ _ _ _ _ _).mpr
      (acceptedCollapsedSource signature typing rules antecedent sorted).property, source_not_derivable⟩

#print axioms source_not_derivable
#print axioms source_representation_collapses
#print axioms collapsed_typed
#print axioms acceptedCollapsedSource
#print axioms acceptedCollapsedSource_checks
end Mettapedia.Languages.MM0.HOLKernelEncodingReflection
