import Mettapedia.OSLF.Framework.FiniteModelContextual
import Mettapedia.OSLF.NativeTypes.Executable.FiniteModelBinderControls

/-!
# Controls: certificates for MeTTaIL's contextual semantics

The languages carry their contexts as authored congruence rules, and the verdicts are about
`ContextualStep.Step`, the least relation those rules generate.

- **λ with full β**: β at the root, and congruences into both sides of an application and under the
  abstraction (`Lam (λ. x) ~> Lam (λ. y) if x ~> y`), so redexes reduce under binders. A clean term
  never reaches a dirty one (`clean_stays_clean_under_full_beta`); the congruence under the binder
  is checked as the monotonicity of the abstraction, and an abstraction that is not monotone fails
  it (`antitone_invalid`).
- **Name passing with authored parallel congruences**: the secret forwarder next to `0` never reaches
  a leaking process (`secret_forwarder_never_leaks_contextual`); with a discarding rule whose freshness
  premise the language's evaluator decides, it still never leaks, for every evaluator that only adds
  bindings (`secret_forwarder_never_leaks_discarding`), the engine's own among them
  (`secret_forwarder_never_leaks_discarding_engine`).
- **Found by search**: the finder runs the contextual semantics too, with the preorder the rules force
  (a least fixed point in which a step joins once its premises hold), and finds two-value certificates
  for full β (`full_beta_never_errs_by_search`) and for the forwarder with authored congruences
  (`secret_forwarder_never_leaks_by_search`); on terms that reach their goals it finds nothing.
- **A rule that moves a metavariable under a new binder** (`Wrap x ~> Lam (λ. x)`): under a binder the
  semantics lifts the wrapped term past the new binder, and wrapping keeps a clean term clean
  (`wrap_stays_clean`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Executable.FiniteModelControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.FiniteModels
open Mettapedia.OSLF.Framework.BackwardSearch
open Mettapedia.OSLF.Framework.HerbrandBridge (Goal)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (BasePremiseEvaluator reducts)

/-- A congruence rule: the metavariable `x` steps to `y` inside the context. -/
def congruenceRule (name : String) (context : Pattern → Pattern) : RewriteRule :=
  { name := name, typeContext := [], premises := [.congruence (.fvar "x") (.fvar "y")],
    left := context (.fvar "x"), right := context (.fvar "y") }

/-! ## λ with full β -/

def fullLambda : LanguageDef :=
  { lambdaCalculus with
    name := "FullLambda"
    rewrites := [beta, congruenceRule "AppLeft" (app · (.fvar "other")),
      congruenceRule "AppRight" (app (.fvar "other") ·), congruenceRule "LamBody" fun body => lam body] }

/-- A redex under a binder: `λx. (λy. y) x`. -/
def underBinder : Pattern := lam (app (lam (.bvar 0)) (.bvar 0))

-- The redex under the binder fires: `λx. (λy. y) x` steps to `λx. x`.
#guard reducts fullLambda 3 underBinder == [lam (.bvar 0)]
-- Applied to `Ok`, β at the root and β under the binder reach the same term.
#guard reducts fullLambda 4 (app underBinder ok) == [app (lam (.bvar 0)) ok, app (lam (.bvar 0)) ok]

theorem full_beta_valid : cleanCertificate.contextualValid fullLambda = true := by decide +kernel

/-- **A clean term never reaches a dirty one**, under β anywhere, including under binders. -/
theorem clean_stays_clean_under_full_beta (base : BasePremiseEvaluator) :
    ¬ Reaches (between (contextualSpan base fullLambda) ObjectState)
      (fun reached => isDirty (value cleanModel reached) = true) (app underBinder ok) :=
  cleanCertificate.cannotReachContextualAccepted_of_check (by decide +kernel) base
    (baseExtends_of_congruencesOnly (by decide +kernel) base)

/-- An abstraction that turns a clean body dirty and a dirty body clean is not monotone, and the
congruence under the binder fails. -/
def antitoneCertificate : Certificate Cleanness :=
  { cleanCertificate with
    model := { cleanModel with lam := fun body => if body .clean == .clean then .dirty else .clean } }

theorem antitone_invalid : antitoneCertificate.contextualValid fullLambda = false := by decide +kernel

/-! ## Name passing with authored parallel congruences -/

def piContextual : LanguageDef :=
  { namePassing with
    name := "NamePassingContextual"
    rewrites := [comm, congruenceRule "ParLeft" (par · (.fvar "other")),
      congruenceRule "ParRight" (par (.fvar "other") ·)] }

#guard reducts piContextual 3 (par secretForwarder nilProcess) == [par (send sec sec) nilProcess]

/-- **The secret forwarder next to `0` never reaches a leaking process**, with the parallel contexts the
language authors. -/
theorem secret_forwarder_never_leaks_contextual (base : BasePremiseEvaluator) :
    ¬ Reaches (between (contextualSpan base piContextual) ObjectState)
      (fun reached => isLeak (value secrecyModel reached) = true) (par secretForwarder nilProcess) :=
  secrecyCertificate.cannotReachContextualAccepted_of_check (by decide +kernel) base
    (baseExtends_of_congruencesOnly (by decide +kernel) base)

/-! ## A rule that moves a metavariable under a new binder -/

/-- `Wrap x ~> Lam (λ. x)`: `x` is captured at depth zero and used under one more binder, so the
semantics lifts its value past the new binder. -/
def wrapRule : RewriteRule :=
  { name := "Wrap", typeContext := [("x", termSort)], premises := [],
    left := .apply "Wrap" [.fvar "x"], right := lam (.fvar "x") }

/-- The wrapping constructor. -/
def wrapTerm : GrammarRule :=
  { label := "Wrap", category := "Term", params := [.simple "x" termSort],
    syntaxPattern := [.terminal "wrap", .nonTerminal "x"] }

def wrapLambda : LanguageDef :=
  { fullLambda with
    name := "WrapLambda"
    «terms» := fullLambda.terms ++ [wrapTerm]
    «rewrites» := fullLambda.rewrites ++ [wrapRule] }

def wrap (term : Pattern) : Pattern := .apply "Wrap" [term]

-- The rule moves a metavariable across a binder.
#guard !Mettapedia.OSLF.MeTTaIL.Match.ruleDepthAligned wrapRule

-- Under a binder, the wrapped variable is lifted past the new one: `λx. wrap x` steps to `λx. λy. x`.
#guard reducts wrapLambda 3 (lam (wrap (.bvar 0))) == [lam (lam (.bvar 1))]

def wrapModel : FiniteModel Cleanness :=
  { cleanModel with
    operation := fun label arguments => match label, arguments with
      | "Wrap", [inner] => inner
      | label, arguments => cleanModel.operation label arguments }

def wrapCertificate : Certificate Cleanness := { cleanCertificate with model := wrapModel }

/-- **Wrapping keeps a clean term clean**, also under binders, where the semantics lifts the wrapped
term. -/
theorem wrap_stays_clean (base : BasePremiseEvaluator) :
    ¬ Reaches (between (contextualSpan base wrapLambda) ObjectState)
      (fun reached => isDirty (value wrapModel reached) = true) (app (lam (wrap (.bvar 0))) ok) :=
  wrapCertificate.cannotReachContextualAccepted_of_check (by decide +kernel) base
    (baseExtends_of_congruencesOnly (by decide +kernel) base)

/-! ## A premise the evaluator decides -/

/-- `Par P Q ~> P` when `x # Q`: the freshness premise is decided by the language's evaluator. -/
def discardRule : RewriteRule :=
  { name := "Discard", typeContext := [], premises := [.freshness ⟨"x", .fvar "Q"⟩],
    left := par (.fvar "P") (.fvar "Q"), right := .fvar "P" }

def piDiscarding : LanguageDef :=
  { piContextual with «rewrites» := piContextual.rewrites ++ [discardRule] }

/-- An evaluator that lets every premise through, keeping the bindings. -/
def everyPremiseHolds : BasePremiseEvaluator := fun _ bindings _ => [bindings]

theorem everyPremiseHolds_extends (language : LanguageDef) : BaseExtends everyPremiseHolds language := by
  intro _ _ _ _ _ bindings result member
  simp only [everyPremiseHolds, List.mem_singleton] at member
  subst member
  exact fun _ _ found => found

/-- **The secret forwarder never leaks, even when compositions may discard their right side**, for any
evaluator of the freshness premise that only adds bindings. -/
theorem secret_forwarder_never_leaks_discarding (base : BasePremiseEvaluator) (fromBase : BaseExtends base piDiscarding) :
    ¬ Reaches (between (contextualSpan base piDiscarding) ObjectState)
      (fun reached => isLeak (value secrecyModel reached) = true) (par secretForwarder nilProcess) :=
  secrecyCertificate.cannotReachContextualAccepted_of_check (by decide +kernel) base fromBase

#guard !congruencesOnly piDiscarding

/-- **The same verdict for the engine's own evaluator of the freshness premise**, the semantics the
executable interpreter runs. -/
theorem secret_forwarder_never_leaks_discarding_engine :
    ¬ Reaches (between (contextualSpan (Mettapedia.OSLF.MeTTaIL.ContextualStep.engineBasePremises
        Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty) piDiscarding) ObjectState)
      (fun reached => isLeak (value secrecyModel reached) = true) (par secretForwarder nilProcess) :=
  secret_forwarder_never_leaks_discarding _ (engine_extends _ _)

/-! ## Contextual certificates found by search -/

/-- The cells the finder assigns for full β from `(λx. (λy. y) x) Ok`. -/
def fullLambdaCells : Cells (Fin 2) :=
  [((4, 3), 1), ((1, 3), 1), ((1, 1), 1), ((0, 1), 1), ((4, 1), 1), ((4, 0), 0), ((3, 0), 1), ((2, 0), 0),
    ((1, 2), 1), ((1, 0), 0), ((0, 0), 0), ((4, 2), 0)]

#guard findCells twoValues 1 lambdaSignature fullLambda [] [err] (app underBinder ok) .contextual ==
  some fullLambdaCells

def fullLambdaSearched : Certificate (Fin 2) :=
  Certificate.ofContextualCells twoValues twoValues_complete 1 lambdaSignature fullLambdaCells fullLambda

/-- **No hand-written model, steps under binders included**: the finder's cells, with the preorder
the rules force, prove that the term never reaches `Err` under full β. -/
theorem full_beta_never_errs_by_search (base : BasePremiseEvaluator) :
    ¬ Reaches (between (contextualSpan base fullLambda) ObjectState) (Goal [err]) (app underBinder ok) :=
  fullLambdaSearched.cannotReachContextual_of_check (accept := fullLambdaSearched.goalAccept [err])
    (by decide +kernel) base (baseExtends_of_congruencesOnly (by decide +kernel) base)

-- `(λx. (λy. Err) x) Ok` reaches `Err`: the finder finds nothing.
#guard findCells twoValues 1 lambdaSignature fullLambda [] [err] (app (lam (app (lam err) (.bvar 0))) ok)
  .contextual == none

def piContextualFoundCells : Cells (Fin 2) :=
  [((2, 3), 1), ((3, 3), 0), ((3, 1), 0), ((6, 3), 1), ((6, 2), 1), ((3, 2), 1), ((6, 1), 1), ((1, 2), 1),
    ((1, 3), 1), ((1, 1), 1), ((2, 1), 1), ((4, 0), 1), ((0, 0), 0), ((1, 0), 0), ((3, 0), 0), ((6, 0), 0),
    ((2, 2), 0), ((2, 0), 0), ((5, 0), 0)]

#guard findCells twoValues 1 piSignature piContextual [] leakNearTop (par secretForwarder nilProcess) .contextual ==
  some piContextualFoundCells

def piContextualSearched : Certificate (Fin 2) :=
  Certificate.ofContextualCells twoValues twoValues_complete 1 piSignature piContextualFoundCells piContextual

/-- **The secret forwarder never leaks, with the authored parallel congruences, by search.** -/
theorem secret_forwarder_never_leaks_by_search (base : BasePremiseEvaluator) :
    ¬ Reaches (between (contextualSpan base piContextual) ObjectState) (Goal leakNearTop)
      (par secretForwarder nilProcess) :=
  piContextualSearched.cannotReachContextual_of_check (accept := piContextualSearched.goalAccept leakNearTop)
    (by decide +kernel) base (baseExtends_of_congruencesOnly (by decide +kernel) base)

#guard findCells twoValues 1 piSignature piContextual [] leakNearTop (par leakyForwarder nilProcess) .contextual == none

end Mettapedia.OSLF.NativeTypes.Executable.FiniteModelControls
