import Mettapedia.Languages.MM0.HOLKernelRuleInstances
import Mettapedia.Logic.HOL.ProofSyntaxHypothesisSubstitution

/-!
# Source proofs for the maintained MM0 nonbinding HOL rules

The raw arguments of each logical or equality rule reconstruct its source
terms and common antecedent. Each successful reading builds an ordinary
HOL proof from the interpreted ordered premises. No source proof is an
input. Hypothesis substitution then composes these local proofs with the
proofs reconstructed at child nodes.

This is the local rule interpretation. Native theorem-table licensing,
agreement with the instantiated native statement, binding rules and checked
definition conversions are separate obligations of proof-tree readback.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.HOLKernelInferenceInterpretation

open Mettapedia.Logic.HOL
open Kernel HOLKernelSyntax HOLKernelTermReadback HOLKernelJudgmentReadback
open NamedElaboration (SomeConst)
open HOLKernelRuleInstances

universe u
variable {Const : Ty Unit → Type u} {gamma : Ctx Unit}

/-- A constructed local proof, with the exact ordered premise list that its
child proof readings must supply. -/
structure InterpretedRule (Const : Ty Unit → Type u) (gamma : Ctx Unit) where
  premises : List (Formula Const gamma)
  conclusion : Formula Const gamma
  proof : ProofSyntax Const premises conclusion

def InterpretedRule.apply (rule : InterpretedRule Const gamma)
    {assumptions : List (Formula Const gamma)}
    (children : ProofSyntax.HypothesisSubstitution rule.premises assumptions) :
    ProofSyntax Const assumptions rule.conclusion :=
  ProofSyntax.substituteHypotheses children rule.proof

def interpretInference {rule : HOLKernelInferenceRules.Rule} (arguments : InferenceArguments Const gamma rule) :
    InterpretedRule Const gamma :=
  ⟨arguments.premises, arguments.conclusion, match arguments with
    | .truth _ => .impI .topI
    | .contradiction _ _ => .impI (.botE (.impE (.hyp 2) (.hyp 0)))
    | .conjunctionIntroduction _ _ _ => .impI (.andI (.impE (.hyp 1) (.hyp 0)) (.impE (.hyp 2) (.hyp 0)))
    | .conjunctionLeft _ _ _ => .impI (.andEL (.impE (.hyp 1) (.hyp 0)))
    | .conjunctionRight _ _ _ => .impI (.andER (.impE (.hyp 1) (.hyp 0)))
    | .disjunctionLeft _ _ _ => .impI (.orIL (.impE (.hyp 1) (.hyp 0)))
    | .disjunctionRight _ _ _ => .impI (.orIR (.impE (.hyp 2) (.hyp 0)))
    | .disjunctionElimination _ _ _ _ => .impI (.orE (.impE (.hyp 1) (.hyp 0))
          (.impE (.hyp 4) (.andI (.hyp 1) (.hyp 0)))
          (.impE (.hyp 5) (.andI (.hyp 1) (.hyp 0))))
    | .implicationIntroduction _ _ _ => .impI (.impI (.impE (.hyp 4) (.andI (.hyp 1) (.hyp 0))))
    | .implicationElimination _ _ _ => .impI (.impE (.impE (.hyp 1) (.hyp 0)) (.impE (.hyp 2) (.hyp 0)))
    | .negationIntroduction _ _ => .impI (.notI (.impE (.impE (.hyp 2) (.hyp 1)) (.hyp 0)))
    | .negationElimination _ _ => .impI (.impI (.notE (.impE (.hyp 2) (.hyp 1)) (.hyp 0)))
    | .reflexivity _ t => .impI (.eqRefl t)
    | .symmetry _ _ _ => .impI (.eqSymm (.impE (.hyp 1) (.hyp 0)))
    | .transitivity _ _ _ _ => .impI (.eqTrans (.impE (.hyp 1) (.hyp 0)) (.impE (.hyp 2) (.hyp 0)))
    | .propositionalExtensionality _ _ _ => .impI (.eqPropI (.impE (.hyp 1) (.hyp 0)) (.impE (.hyp 2) (.hyp 0)))
    | .equalityImplicationLeft _ _ _ => .impI (.eqPropEL (.impE (.hyp 1) (.hyp 0)))
    | .equalityImplicationRight _ _ _ => .impI (.eqPropER (.impE (.hyp 1) (.hyp 0)))
    | .applicationFunction _ t _ _ => .impI (.eqApp t (.impE (.hyp 1) (.hyp 0)))
    | .applicationArgument _ _ _ f => .impI (.eqAppArg f (.impE (.hyp 2) (.hyp 0)))
    | .booleanEqualityElimination _ _ _ => .impI (.impE (.eqPropEL (.impE (.hyp 1) (.hyp 0)))
          (.impE (.hyp 2) (.hyp 0)))⟩

def interpretStructural {rule : HOLKernelStructuralRules.Rule} (arguments : StructuralArguments Const gamma rule) :
    InterpretedRule Const gamma :=
  ⟨arguments.premises, arguments.conclusion, match arguments with
    | .id _ => .impI (.hyp 0)
    | .syl _ _ _ => .impI (.impE (.hyp 2) (.impE (.hyp 1) (.hyp 0)))
    | .ian _ _ _ => .impI (.andI (.impE (.hyp 1) (.hyp 0)) (.impE (.hyp 2) (.hyp 0)))
    | .anl _ _ => .impI (.andEL (.hyp 0))
    | .anr _ _ => .impI (.andER (.hyp 0))⟩

def readInferenceWith (reader : TermReader Const) (references : HOLKernelSyntax.Symbol → Nat)
    (names : Names gamma) (rule : HOLKernelInferenceRules.Rule)
    (arguments : List Preterm) : Option (InterpretedRule Const gamma) :=
  (readInferenceArguments reader references names rule arguments).map interpretInference

def readStructuralWith (reader : TermReader Const) (references : HOLKernelSyntax.Symbol → Nat)
    (names : Names gamma) (rule : HOLKernelStructuralRules.Rule)
    (arguments : List Preterm) : Option (InterpretedRule Const gamma) :=
  (readStructuralArguments reader references names rule arguments).map interpretStructural

def readObject (references : HOLKernelSyntax.Symbol → Nat)
    (constants : Nat → Option (SomeConst Const)) (parameters : Nat)
    (names : Names gamma) (type : Ty Unit) (native : Preterm) : Option (Term Const gamma type) :=
  readObjectWith (readTerm references constants parameters) names type native

def readInference (references : HOLKernelSyntax.Symbol → Nat)
    (constants : Nat → Option (SomeConst Const)) (parameters : Nat)
    (names : Names gamma) (rule : HOLKernelInferenceRules.Rule)
    (arguments : List Preterm) : Option (InterpretedRule Const gamma) :=
  readInferenceWith (readTerm references constants parameters) references names rule arguments

def readStructural (references : HOLKernelSyntax.Symbol → Nat)
    (constants : Nat → Option (SomeConst Const)) (parameters : Nat)
    (names : Names gamma) (rule : HOLKernelStructuralRules.Rule)
    (arguments : List Preterm) : Option (InterpretedRule Const gamma) :=
  readStructuralWith (readTerm references constants parameters) references names rule arguments

#print axioms readInference
#print axioms readStructural
#print axioms InterpretedRule.apply

end Mettapedia.Languages.MM0.HOLKernelInferenceInterpretation
