import Mettapedia.OSLF.NativeTypes.Instances.Lambda.Generated

open Mettapedia.OSLF.Framework

/-!
# Scoped lambda generated-judgment controls

These use the original constructor catalogue, capture-avoiding substitution
and contextual engine. The mixed-successor tests distinguish existential
from outgoing-universal questions, and coincident targets retain both
congruence histories.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.Lambda.Controls

open Mettapedia.OSLF.Binding
open LambdaContextualRung LambdaScopedAuthoringComparison
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.NativeTypes.Decision.Reference.Core
open Mettapedia.OSLF.NativeTypes.Instances.Lambda.Generated

def identity : Term sig [] .term := lamT (.var .zero)
def redex : Term sig [] .term := appT identity identity
def mixed : Term sig [] .term := appT redex redex
def selfApply : Term sig [] .term := lamT (appT (.var .zero) (.var .zero))
def omegaTerm : Term sig [] .term := appT selfApply selfApply
def duplicate : Term sig [] .term := appT omegaTerm omegaTerm

def captureSource : Term sig [.term] .term :=
  appT (lamT (lamT (.var (.succ .zero)))) (.var .zero)
def captureTarget : Term sig [.term] .term := lamT (.var (.succ .zero))
def capturedIncorrectly : Term sig [.term] .term := lamT (.var .zero)

def underLambda : Term sig [] .term :=
  lamT (appT (lamT (.var .zero)) (.var .zero))

def observe (label : String) (make : Formula Leaf → Formula Leaf)
    {Γ : Ctx sig} (program : Term sig Γ .term) (budget : Nat) : Option (Option Bool) := do
  let leaf ← former? label
  return (run {} Γ (make (.atom leaf)) program budget).answer

def targets {Γ : Ctx sig} (program : Term sig Γ .term) : List Pattern :=
  (Mettapedia.OSLF.NativeTypes.Instances.Lambda.Frontier.firings {} program).map fun receipt => encodeTerm receipt.target

def hasLambdaHead : Pattern → Bool
  | .apply "Lam" [_] => true
  | _ => false

def leftLambda? : Option Leaf := do
  let former ← former? "App"
  return {former with accepts := fun position source =>
    if position.val = 0 then hasLambdaHead source else true}

def mixedQuestion (make : Formula Leaf → Formula Leaf) : Option (Option Bool) := do
  let former ← leftLambda?
  return (run {} [] (make (.atom former)) mixed 20).answer

#guard formers.map (fun leaf => (Mettapedia.OSLF.NativeTypes.Generation.structuralDeclaration generated leaf.index).label) ==
  ["App", "Lam"]
#guard observe "Lam" id identity 1 == some (some true)
#guard observe "App" id identity 1 == some (some false)
#guard observe "Lam" Formula.neg identity 2 == some (some false)
#guard observe "Lam" Formula.possibility redex 0 == some none
#guard observe "Lam" Formula.possibility redex 20 == some (some true)
#guard observe "App" Formula.possibility redex 20 == some (some false)
#guard observe "Lam" Formula.outgoingUniversal redex 20 == some (some true)
#guard observe "App" Formula.outgoingUniversal redex 20 == some (some false)
#guard observe "Lam" (fun leaf => .conj .top (.possibility leaf)) redex 20 == some (some true)
#guard observe "Lam" (fun leaf => .imp .top (.possibility leaf)) redex 20 == some (some true)
#guard (run {} [] (.possibility .top) identity 20).answer == some false
#guard (run {} [] (.outgoingUniversal .bottom) identity 20).answer == some true
#guard (run {} [] (.possibility (.possibility .top)) redex 20).answer == some false
#guard mixedQuestion Formula.possibility == some (some true)
#guard mixedQuestion Formula.outgoingUniversal == some (some false)
#guard targets redex == [encodeTerm identity]
#guard targets captureSource == [encodeTerm captureTarget]
#guard !(targets captureSource).contains (encodeTerm capturedIncorrectly)
#guard targets duplicate == [encodeTerm duplicate, encodeTerm duplicate]
#guard (Mettapedia.OSLF.NativeTypes.Instances.Lambda.Frontier.firings {} duplicate).map
    (fun receipt => match receipt.history with | .fire index _ => index) == [2, 3]
#guard (run {} [] (.possibility .top) underLambda 20).answer == some true
#guard (run {lamCong := false} [] (.possibility .top) underLambda 20).answer == some false
#guard (Mettapedia.OSLF.NativeTypes.Instances.Lambda.Decode.decode [] (.bvar 0)).isNone
#guard (Mettapedia.OSLF.NativeTypes.Instances.Lambda.Decode.decode [] (.apply "App" [])).isNone
#guard (Mettapedia.OSLF.NativeTypes.Instances.Lambda.Decode.decode [] (.apply "PZero" [])).isNone

theorem duplicate_origins_retained :
    (Mettapedia.OSLF.NativeTypes.Instances.Lambda.Frontier.firings {} duplicate).map (·.history) =
      [.fire 2 [.step 0 0 (.fire 0 [])], .fire 3 [.step 0 0 (.fire 0 [])]] := by
  simp [duplicate, omegaTerm, selfApply, appT, lamT,
    Mettapedia.OSLF.NativeTypes.Instances.Lambda.Frontier.firings, Mettapedia.OSLF.NativeTypes.Instances.Lambda.Frontier.betaFirings,
    Mettapedia.OSLF.NativeTypes.Instances.Lambda.Frontier.betaAtApp, Mettapedia.OSLF.NativeTypes.Instances.Lambda.Frontier.liftAppL,
    Mettapedia.OSLF.NativeTypes.Instances.Lambda.Frontier.liftAppR]
  rfl

theorem original_engine_exact_for_every_source {Γ : Ctx sig} (source target : Term sig Γ .term) :
    (∃ history, (history, encodeTerm target) ∈
      Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution.rewriteAt
        Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty LambdaAuthoredFullRuleProfile.language
        (Mettapedia.OSLF.NativeTypes.Instances.Lambda.Frontier.nodeCount source) Γ.length (encodeTerm source)) ↔
      Step Γ source target :=
  Mettapedia.OSLF.NativeTypes.Instances.Lambda.Backend.authored_successors_exact source target _ (Nat.le_refl _)

theorem all_generated_questions_complete (formula : Formula Leaf) :
    (run {} [] formula mixed (decisionBound {} [] formula mixed)).Decided :=
  whole_language_complete {} [] formula mixed

end Mettapedia.OSLF.NativeTypes.Instances.Lambda.Controls
