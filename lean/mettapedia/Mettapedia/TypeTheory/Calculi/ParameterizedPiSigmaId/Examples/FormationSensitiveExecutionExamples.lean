import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveExecution
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.CumulativePreservation
import Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.CumulativeEmbedding

/-!
# Typed contextual execution controls in the existing simple fragment

Both executions apply the same identity function twice to the same supplied
argument. One contracts inside the argument first; the other contracts the
outer application first. They retain different structural receipts while
preserving the same actual formation-sensitive judgment.

The profile has no declaration-specific root rules. These controls instantiate
native beta computation, not an interpretation of a complete guest checker.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace FormationSensitive.Execution.Examples

open ProofRelevantStructuralComputation
open Mettapedia.GSLT.Ultrainfinite (Route)
open Mettapedia.TypeTheory.Calculi.SingleBaseSTLC

def roots : Declaration.ProofRelevantRootComputation Tower.Head :=
  Canary.emptyComputation Tower.Head

theorem root_support : Tower.rules.computation = roots.support := by
  change RootComputation.empty = roots.support
  unfold RootComputation.empty roots Canary.emptyComputation
    Declaration.ProofRelevantRootComputation.support
  congr
  funext n left right
  apply propext
  constructor
  · intro impossible
    exact False.elim impossible
  · rintro ⟨impossible⟩
    exact Empty.elim impossible

def identity {context : List IntrinsicSTT.Ty} :
    IntrinsicSTT.Term context (.arr .atom .atom) := .lam (.var .zero)

def source : IntrinsicSTT.Term [.atom] .atom :=
  .app identity (.app identity (.var .zero))

def context : Tower.Ctx 1 := TowerDTT.eraseContext [.atom]
def start : Tower.Tm 1 := TowerDTT.eraseTerm source
def middle : Tower.Tm 1 := .app (.lam (.var 0)) (.var 0)
def finish : Tower.Tm 1 := .var 0
def type : Tower.Tm 1 := .head .legacyGround

def beta (argument : Tower.Tm 1) :
    StructuralStepReceipt roots Tower.rules.headEq
      (.app (.lam (.var 0)) argument) argument := by
  simpa only [inst0, subst0, subst, Fin.cases_zero] using
    (StructuralStepReceipt.betaPi (computation := roots)
      (headEq := Tower.rules.headEq) (.var 0) argument)

def innerFirst : Path roots Tower.rules.headEq start finish :=
  .cons (.congAppArg (beta finish)) (.cons (beta finish) (.refl finish))

def outerFirst : Path roots Tower.rules.headEq start finish :=
  .cons (beta middle) (.cons (beta finish) (.refl finish))

private theorem identityTyped {arity : Nat} (environment : Tower.Ctx arity) :
    Typing Tower.rules environment (.lam (.var 0))
      (.pi (.head .legacyGround) (.head .legacyGround)) := by
  refine Typing.lamIntro (R := Tower.rules)
    (u := .sort (.max Tower.zero Tower.zero)) ?_ (.sort _) ?_
  · exact .piForm (.headType .legacyGround) (.sort Tower.zero)
      (.headType .legacyGround) (.sort Tower.zero) (.sorts Tower.zero Tower.zero)
  · simpa only [Ctx.lookup_snoc_zero, rename] using
      (Typing.var (R := Tower.rules) (Γ := .snoc environment (.head .legacyGround)) 0)

theorem sourceJudgment : Judgment Tower.rules context start type := by
  refine ⟨.snoc .nil (.headType .legacyGround) (.sort Tower.zero), ?_⟩
  have argument : Typing Tower.rules context finish type := by
    simpa only [context, TowerDTT.eraseContext, TowerDTT.eraseTypeAt,
      Ctx.lookup_snoc_zero, rename, type, finish] using
      (Typing.var (R := Tower.rules) (Γ := context) 0)
  exact Typing.appElim (identityTyped context)
    (Typing.appElim (identityTyped context) argument)

def typedInnerFirst : TypedPath Tower.rules roots context start finish type :=
  ⟨sourceJudgment, innerFirst⟩

def typedOuterFirst : TypedPath Tower.rules roots context start finish type :=
  ⟨sourceJudgment, outerFirst⟩

theorem endpoint_judgment : Judgment Tower.rules context finish type :=
  innerFirst.preserves root_support towerUniverseRegularity LevelTower.piConversionBoundary
    (EmptyRootConversion.sigmaConversionBoundary Tower.rules rfl LevelTower.headEq_symmetric)
    towerHeadPreservation towerRootPreservation typedInnerFirst.sourceJudgment

theorem both_retain_two_steps :
    innerFirst.length = 2 ∧ outerFirst.length = 2 := by
  constructor <;> rfl

def beginsInArgument {left right : Tower.Tm 1}
    (path : Path roots Tower.rules.headEq left right) : Bool :=
  match path with
  | .cons (.congAppArg _) _ => true
  | _ => false

theorem same_endpoint_different_receipts : typedInnerFirst ≠ typedOuterFirst := by
  apply TypedPath.distinct_of_paths
  intro same
  have impossible := congrArg beginsInArgument same
  change true = false at impossible
  cases impossible

end FormationSensitive.Execution.Examples
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
