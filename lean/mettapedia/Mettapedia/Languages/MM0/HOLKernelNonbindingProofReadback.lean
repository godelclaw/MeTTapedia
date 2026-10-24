import Mettapedia.Languages.MM0.HOLKernelProofReadbackCore

/-!
# Nonbinding instance of the context-indexed HOL proof reader

The shared fold reconstructs native formation, structural and nonbinding
inference, and checked conversions that preserve the source reading. This
instance admits no additional binding handler. The full reader extends the
same fold with context-changing rule interpretations.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.MM0.HOLKernelNonbindingProofReadback
open Mettapedia.Logic.HOL
open Kernel HOLKernelSyntax HOLKernelTermReadback HOLKernelRuleReadback HOLKernelProofReadback
open NamedElaboration (SomeConst)
universe u
variable {Const : Ty Unit → Type u} {gamma : Ctx Unit}
variable {terms : TermSignature} {definitions : Definition.Signature}
variable {references : HOLKernelSyntax.Symbol → Nat} {ids : SortIds}

def readProof [∀ type, DecidableEq (Const type)]
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions references ids)
    (theorems : TheoremSignature) (context : Context)
    (reader : TermReader Const) (parameters : Nat) (names : Names gamma)
    (ruleAt : Nat → Option Rule) (fuel : Nat) (witness : ProofWitness) :
    Option (ProofReadback abbreviation theorems context reader parameters names witness) :=
  readProofWith abbreviation theorems context reader parameters ruleAt
    (fun _ {_} _ _ _ _ _ => none) names fuel witness

#print axioms readProof
end Mettapedia.Languages.MM0.HOLKernelNonbindingProofReadback
