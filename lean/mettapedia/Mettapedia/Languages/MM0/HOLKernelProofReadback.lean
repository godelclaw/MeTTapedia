import Mettapedia.Languages.MM0.HOLKernelBindingInterpretation

/-!
# Native HOL proof readback with explicit binding-rule authority

The context-indexed fold combines structural and nonbinding rule readings
with the licensed binding interpretation. Native acceptance is checked
independently. Every successful result contains an ordinary HOL proof and
the exact source reading of its actual native conclusion.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.MM0.HOLKernelProofReadback
open Mettapedia.Logic.HOL
open Kernel HOLKernelSyntax HOLKernelTermReadback HOLKernelRuleReadback
open NamedElaboration (SomeConst)
universe u
variable {Const : Ty Unit → Type u} {gamma : Ctx Unit}
variable {terms : TermSignature} {definitions : Definition.Signature}
variable {references : HOLKernelSyntax.Symbol → Nat} {ids : SortIds}

def readProof [∀ type, DecidableEq (Const type)]
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions references ids)
    (theorems : TheoremSignature) (context : Context)
    (reader : TermReader Const) (parameters : Nat) (names : Names gamma)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (fuel : Nat) (witness : ProofWitness) :
    Option (ProofReadback abbreviation theorems context reader parameters names witness) :=
  readProofWith abbreviation theorems context reader parameters ruleAt
    (HOLKernelBindingInterpretation.readBinding bindingAt) names fuel witness

/-- Proof-free tree admission of a native MM0 proof witness across arbitrary
context-changing binding steps, nonbinding rule applications, formation steps,
and beta-joinable conversions. -/
def AdmittedProof
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions references ids)
    (theorems : TheoremSignature) (context : Context)
    (reader : TermReader Const) (parameters : Nat)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule) :
    (fuel : Nat) → {gamma : Ctx Unit} → Names gamma → ProofWitness → Formula Const gamma → Type u
  | 0, _, _, _, _ => PEmpty
  | fuel + 1, _, names, witness, formula =>
      AdmittedStep abbreviation theorems context reader parameters ruleAt
        (HOLKernelBindingInterpretation.AdmittedBinding abbreviation theorems reader parameters bindingAt)
        (fun nextNames child childFormula =>
          AdmittedProof abbreviation theorems context reader parameters ruleAt bindingAt fuel
            nextNames child childFormula)
        names witness formula

/-- Increasing the recursion budget preserves admission without changing
the certificate, source formula or variable frame. -/
def AdmittedProof.weakenFuel
    {abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions references ids}
    {theorems : TheoremSignature} {context : Context}
    {reader : TermReader Const} {parameters : Nat}
    {ruleAt : Nat → Option Rule} {bindingAt : Nat → Option HOLKernelBindingRules.Rule}
    {fuel larger : Nat} {names : Names gamma} {witness : ProofWitness} {formula : Formula Const gamma}
    (budget : fuel ≤ larger)
    (admitted : AdmittedProof abbreviation theorems context reader parameters ruleAt bindingAt
      fuel names witness formula) :
    AdmittedProof abbreviation theorems context reader parameters ruleAt bindingAt
      larger names witness formula := by
  induction fuel generalizing larger gamma names witness formula with
  | zero => cases admitted
  | succ fuel ih =>
      cases larger with
      | zero => omega
      | succ larger =>
          exact AdmittedStep.mapChildren
            (fun child => ih (Nat.le_of_succ_le_succ budget) child)
            (fun binding => binding.mapChildren
              (fun child => ih (Nat.le_of_succ_le_succ budget) child))
            admitted

theorem readProof_of_admitted [∀ type, DecidableEq (Const type)]
    {abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions references ids}
    {theorems : TheoremSignature} {context : Context}
    {reader : TermReader Const} {parameters : Nat}
    {ruleAt : Nat → Option Rule} {bindingAt : Nat → Option HOLKernelBindingRules.Rule}
    {fuel : Nat} {names : Names gamma} {witness : ProofWitness} {formula : Formula Const gamma}
    (admitted : AdmittedProof abbreviation theorems context reader parameters ruleAt bindingAt
      fuel names witness formula) :
    ∃ out : ProofReadback abbreviation theorems context reader parameters names witness,
      readProof abbreviation theorems context reader parameters names ruleAt bindingAt fuel witness = some out ∧
      out.source.formula = formula := by
  induction fuel generalizing gamma names witness formula with
  | zero => cases admitted
  | succ fuel ih =>
      exact readProofWith_of_admitted
        (fun nextNames child childFormula childAdmitted => ih childAdmitted)
        (fun recurse childrenOk _ _ _ _ _ _ bindingAdmitted =>
          HOLKernelBindingInterpretation.readBinding_of_admitted childrenOk bindingAdmitted)
        admitted

#print axioms readProof
#print axioms AdmittedProof.weakenFuel
#print axioms readProof_of_admitted
theorem AdmittedProof.accepted
    {abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions references ids}
    {theorems : TheoremSignature} {context : Context} {reader : TermReader Const}
    {parameters : Nat} {ruleAt : Nat → Option Rule} {bindingAt : Nat → Option HOLKernelBindingRules.Rule}
    {fuel : Nat} {names : Names gamma} {witness : ProofWitness} {formula : Formula Const gamma}
    (admitted : AdmittedProof abbreviation theorems context reader parameters ruleAt bindingAt fuel names witness formula) :
    ∃ native, witness.proof? terms definitions theorems context [] = some native := by
  cases fuel with
  | zero => cases admitted
  | succ fuel => cases admitted <;> exact ⟨_, by assumption⟩

end Mettapedia.Languages.MM0.HOLKernelProofReadback
