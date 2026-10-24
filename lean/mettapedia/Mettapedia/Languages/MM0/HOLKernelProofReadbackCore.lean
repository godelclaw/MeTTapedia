import Mettapedia.Languages.MM0.HOLKernelRuleReadback
import Mettapedia.Logic.HOL.ConversionNormalizationRecipes

/-!
# Context-indexed reconstruction of native HOL proof trees

The shared fold checks the actual native witness, reads formation and
nonbinding inference, and substitutes reconstructed child proofs in their
declaration order. A binding handler receives recursive readers at arbitrary
intrinsic variable frames. It must construct a source proof and establish its
exact reading of the native conclusion; supplying only a statement is
insufficient.

Fuel bounds the recursive computation. Native acceptance, intrinsic source
proof syntax and the equality of the read conclusion remain separate data.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.MM0.HOLKernelProofReadback

open Mettapedia.Logic.HOL
open Kernel HOLKernelSyntax HOLKernelTermReadback HOLKernelRuleReadback
open NamedElaboration (SomeConst)

universe u
variable {Const : Ty Unit → Type u} {gamma : Ctx Unit}

structure ProvedFormula (Const : Ty Unit → Type u) (gamma : Ctx Unit) where
  formula : Formula Const gamma
  proof : ProofSyntax Const [] formula

def supplyChildren [∀ type, DecidableEq (Const type)] :
    (expected : List (Formula Const gamma)) → List (ProvedFormula Const gamma) →
    Option (ProofSyntax.HypothesisSubstitution expected [])
  | [], [] => some (fun occurrence => Fin.elim0 occurrence)
  | formula :: rest, child :: children =>
      if same : child.formula = formula then do
        let tail ← supplyChildren rest children
        pure (Fin.cases (same ▸ child.proof) tail)
      else none
  | _, _ => none

variable {terms : TermSignature} {definitions : Definition.Signature}
variable {references : HOLKernelSyntax.Symbol → Nat} {ids : SortIds}

structure SourceReading
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions references ids)
    (reader : TermReader Const) (parameters : Nat) (names : Names gamma)
    (native : Preterm) where
  source : ProvedFormula Const gamma
  reading : readFormulaIn abbreviation reader parameters names native = some source.formula

structure ProofReadback
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions references ids)
    (theorems : TheoremSignature) (context : Context)
    (reader : TermReader Const) (parameters : Nat) (names : Names gamma)
    (witness : ProofWitness) where
  native : Preterm
  accepted : witness.proof? terms definitions theorems context [] = some native
  source : ProvedFormula Const gamma
  reading : readFormulaIn abbreviation reader parameters names native = some source.formula

abbrev Reader
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions references ids)
    (theorems : TheoremSignature) (context : Context)
    (reader : TermReader Const) (parameters : Nat) :=
  {gamma : Ctx Unit} → (names : Names gamma) → (witness : ProofWitness) →
    Option (ProofReadback abbreviation theorems context reader parameters names witness)

abbrev BindingHandler
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions references ids)
    (theorems : TheoremSignature) (context : Context)
    (reader : TermReader Const) (parameters : Nat) :=
  Reader abbreviation theorems context reader parameters →
    {gamma : Ctx Unit} → (names : Names gamma) → Nat → List Preterm → List ProofWitness →
    (native : Preterm) → Option (SourceReading abbreviation reader parameters names native)

def readProofWith [∀ type, DecidableEq (Const type)]
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions references ids)
    (theorems : TheoremSignature) (context : Context)
    (reader : TermReader Const) (parameters : Nat)
    (ruleAt : Nat → Option Rule)
    (binding : BindingHandler abbreviation theorems context reader parameters)
    {gamma : Ctx Unit} (names : Names gamma) : (fuel : Nat) → (witness : ProofWitness) →
    Option (ProofReadback abbreviation theorems context reader parameters names witness)
  | 0, _ => none
  | fuel + 1, witness =>
      match accepted : witness.proof? terms definitions theorems context [] with
      | none => none
      | some native =>
          match formation : HOLKernelJudgmentReadback.readJudgmentWith reader references names
              (expandEquivalence references abbreviation.reference native) with
          | some (.consequence antecedent (.typing _)) =>
              some ⟨native, accepted, ⟨.imp antecedent.formula .top, .impI .topI⟩,
                by simp [readFormulaIn, formation, HOLKernelJudgmentReadback.Judgment.formula]⟩
          | _ =>
              let recurse : Reader abbreviation theorems context reader parameters :=
                fun nextNames child =>
                  readProofWith abbreviation theorems context reader parameters ruleAt binding nextNames fuel child
              match witness with
              | .hyp _ => none
              | .theoremApp index arguments children =>
                  let standard : Option (SourceReading abbreviation reader parameters names native) := do
                    let application ← readApplication abbreviation theorems context reader parameters names
                      ruleAt index arguments
                    if same : application.native.conclusion = native then
                      let reconstructed ← children.mapM fun child => (recurse names child).map ProofReadback.source
                      let supplied ← supplyChildren application.interpretation.source.premises reconstructed
                      pure ⟨⟨application.interpretation.source.conclusion, application.apply supplied⟩,
                        same ▸ application.interpretation.conclusion_read⟩
                    else none
                  match standard with
                  | some source => some ⟨native, accepted, source.source, source.reading⟩
                  | none =>
                      (binding recurse names index arguments children native).map fun source =>
                        ⟨native, accepted, source.source, source.reading⟩
              | .conversion _ child => do
                  let reconstructed ← recurse names child
                  match reading : readFormulaIn abbreviation reader parameters names native with
                  | none => none
                  | some formula =>
                      if same : reconstructed.source.formula = formula then
                        pure ⟨native, accepted, ⟨formula, same ▸ reconstructed.source.proof⟩, reading⟩
                      else
                        (Mettapedia.Logic.HOL.ConversionRecipes.betaConvertProof?
                          formula reconstructed.source.proof).map fun proof =>
                            ⟨native, accepted, ⟨formula, proof⟩, reading⟩

theorem ProofReadback.native_checked
    {abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions references ids}
    {theorems : TheoremSignature} {context : Context}
    {reader : TermReader Const} {parameters : Nat} {names : Names gamma}
    {witness : ProofWitness}
    (reconstructed : ProofReadback abbreviation theorems context reader parameters names witness) :
    witness.check terms definitions theorems context [] reconstructed.native = true :=
  (ProofWitness.check_iff _ _ _ _ _ _ _).mpr (ProofWitness.proof_sound reconstructed.accepted)

theorem ProofReadback.source_derivation
    {abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions references ids}
    {theorems : TheoremSignature} {context : Context}
    {reader : TermReader Const} {parameters : Nat} {names : Names gamma}
    {witness : ProofWitness}
    (reconstructed : ProofReadback abbreviation theorems context reader parameters names witness) :
    ExtDerivation Const [] reconstructed.source.formula := reconstructed.source.proof.erase

#print axioms readProofWith
#print axioms ProofReadback.native_checked
#print axioms ProofReadback.source_derivation

end Mettapedia.Languages.MM0.HOLKernelProofReadback
