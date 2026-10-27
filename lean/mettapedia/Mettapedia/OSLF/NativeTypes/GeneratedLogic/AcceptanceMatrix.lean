import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CountingControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.ClosedControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CanonicalRegionControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CanonicalUnwrapControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Verdicts
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Hints

/-!
# The acceptance matrix of the front door

Rows `ask L q budget` with their expected answers, for λ with full β, over seven terms and twelve
formulas. The terms are a value, a redex, a redex under a binder, two terms with two redexes each (one
result, two results), Ω, and a term that grows forever. The formulas cover steps, stuckness, reachability,
safety, termination, divergence, a ν over μ alternation, counting, a constructor former and a
singleton.

Each row reads an answer and the evidence that settled it:

- `P` or `R`: proved or refuted;
- `certificate`: a finite-model certificate, the cells the finder produces for the row's formula and term
  (`askFound`), given as the hint;
- `exploration`: the region the term reaches;
- `closed`: a closed region;
- `canonical`: a closed canonical region, for a language with equations given canonical forms;
- `open`: no evidence within the budget.

Soundness of every row is `ask_proved` and `ask_refuted`. The rows check that the front door answers,
and with which evidence: premise fuel three and six rounds. The rows are data (`lambdaRows`, `aliasRows`,
`unwrapRows`), checked here and written out, with the languages, as the command-line executable's matrix. The term under a binder needs more fuel for
its region to close, and the growing term has infinitely many states, so universal claims about both stay
open.

A second grid asks about the constants of a language with the equation `A = B` and the rule `B ⇒ C`, over
six formulas, with and without its canonical forms. With them every row is decided. Without them only
what the region a term reaches shows is decided: `B` steps, and `C` is `C`.

A third grid asks about terms of a language with the equation `Wrap x = x` and the rule `Pair x y ⇒ x`,
over four formulas, with and without its canonical forms. With them every row is decided. Without them
only one is: `Pair (Wrap Ok) Err` steps. That it reaches `Ok` needs the equation, since it steps to
`Wrap Ok`.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.AcceptanceMatrix

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.Verdicts (answerSummary)
open Mettapedia.OSLF.NativeTypes.Executable.FiniteModelControls (fullLambda underBinder app lam ok err)
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.CertificateControls (safety reachesErr)
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.SearchControls (runsEnd growing)
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.ClosedControls (runsForever okStaysReachable omegaTerm)
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.CountingControls
  (distinctResults atMostOne deterministic sameResult twoResults)

/-- The premise fuel of the λ grid. -/
def lambdaFuel : ℕ := 3

/-- The rounds of the λ grid. -/
def lambdaRounds : ℕ := 6

/-- The row's answer: full β, premise fuel three, the finder's cells over two values as the hint, six rounds. -/
def summary (term : Pattern) (formula : Formula 0) : String :=
  answerSummary (askFound RelationEnv.empty fullLambda lambdaFuel formula term 1 lambdaRounds)

/-- Some step. -/
def canStep : Formula 0 := .possibly .any .top

/-- No step. -/
def stuck : Formula 0 := .necessarily .any .bot

/-- Built by application from two arguments. -/
def builtApp : Formula 0 := .built "App" (.cons .top (.cons .top .nil))

/-- The term `ok`. -/
def isOk : Formula 0 := .is ok

/-- `(λx. Err) ok`. -/
def errAfterOne : Pattern := app (lam err) ok

/-- `(λx. (λy. y) x) ok`. -/
def underBinderOk : Pattern := app underBinder ok

/-- **The rows of the λ grid**: a term, a formula and the expected answer. -/
def lambdaRows : List (Pattern × Formula 0 × String) := [
  -- `ok`
  (ok, canStep, "R closed"),
  (ok, stuck, "P closed"),
  (ok, reachesErr, "R certificate"),
  (ok, safety, "P certificate"),
  (ok, runsEnd, "P closed"),
  (ok, runsForever, "R closed"),
  (ok, okStaysReachable, "P closed"),
  (ok, (distinctResults 2), "R closed"),
  (ok, atMostOne, "P closed"),
  (ok, deterministic, "R closed"),
  (ok, builtApp, "R closed"),
  (ok, isOk, "P exploration"),
  -- `errAfterOne`
  (errAfterOne, canStep, "P exploration"),
  (errAfterOne, stuck, "R exploration"),
  (errAfterOne, reachesErr, "P exploration"),
  (errAfterOne, safety, "R exploration"),
  (errAfterOne, runsEnd, "P closed"),
  (errAfterOne, runsForever, "R closed"),
  (errAfterOne, okStaysReachable, "R closed"),
  (errAfterOne, (distinctResults 2), "R closed"),
  (errAfterOne, atMostOne, "P closed"),
  (errAfterOne, deterministic, "P closed"),
  (errAfterOne, builtApp, "P closed"),
  (errAfterOne, isOk, "R closed"),
  -- `underBinder`
  (underBinderOk, canStep, "P exploration"),
  (underBinderOk, stuck, "R exploration"),
  (underBinderOk, reachesErr, "R certificate"),
  (underBinderOk, safety, "P certificate"),
  (underBinderOk, runsEnd, "open"),
  (underBinderOk, runsForever, "open"),
  (underBinderOk, okStaysReachable, "open"),
  (underBinderOk, (distinctResults 2), "open"),
  (underBinderOk, atMostOne, "open"),
  (underBinderOk, deterministic, "open"),
  (underBinderOk, builtApp, "open"),
  (underBinderOk, isOk, "open"),
  -- `sameResult`
  (sameResult, canStep, "P exploration"),
  (sameResult, stuck, "R exploration"),
  (sameResult, reachesErr, "R certificate"),
  (sameResult, safety, "P certificate"),
  (sameResult, runsEnd, "P closed"),
  (sameResult, runsForever, "R closed"),
  (sameResult, okStaysReachable, "P closed"),
  (sameResult, (distinctResults 2), "R closed"),
  (sameResult, atMostOne, "P closed"),
  (sameResult, deterministic, "P closed"),
  (sameResult, builtApp, "P closed"),
  (sameResult, isOk, "R closed"),
  -- `twoResults`
  (twoResults, canStep, "P exploration"),
  (twoResults, stuck, "R exploration"),
  (twoResults, reachesErr, "R certificate"),
  (twoResults, safety, "P certificate"),
  (twoResults, runsEnd, "P closed"),
  (twoResults, runsForever, "R closed"),
  (twoResults, okStaysReachable, "P closed"),
  (twoResults, (distinctResults 2), "P closed"),
  (twoResults, atMostOne, "R closed"),
  (twoResults, deterministic, "R closed"),
  (twoResults, builtApp, "P closed"),
  (twoResults, isOk, "R closed"),
  -- `omega`
  (omegaTerm, canStep, "P exploration"),
  (omegaTerm, stuck, "R exploration"),
  (omegaTerm, reachesErr, "R certificate"),
  (omegaTerm, safety, "P certificate"),
  (omegaTerm, runsEnd, "R exploration"),
  (omegaTerm, runsForever, "P exploration"),
  (omegaTerm, okStaysReachable, "R closed"),
  (omegaTerm, (distinctResults 2), "R closed"),
  (omegaTerm, atMostOne, "P closed"),
  (omegaTerm, deterministic, "P closed"),
  (omegaTerm, builtApp, "P closed"),
  (omegaTerm, isOk, "R closed"),
  -- `growing`
  (growing, canStep, "P exploration"),
  (growing, stuck, "R exploration"),
  (growing, reachesErr, "R certificate"),
  (growing, safety, "P certificate"),
  (growing, runsEnd, "open"),
  (growing, runsForever, "open"),
  (growing, okStaysReachable, "open"),
  (growing, (distinctResults 2), "open"),
  (growing, atMostOne, "open"),
  (growing, deterministic, "open"),
  (growing, builtApp, "open"),
  (growing, isOk, "open")]

#guard lambdaRows.all fun (term, formula, expected) => summary term formula == expected

/-! ## Modulo an equation -/

open Mettapedia.OSLF.NativeTypes.GeneratedLogic.CanonicalRegionControls
  (aliased aliasForms constant steps reachesC twoSteps isB isNotC oneResult)

/-- The row's answer given the canonical forms: premise fuel two, two rounds. -/
def summaryModulo (term : Pattern) (formula : Formula 0) : String :=
  answerSummary (askFound RelationEnv.empty aliased 2 formula term 1 2 (some aliasForms))

/-- The row's answer without them. -/
def summaryAsWritten (term : Pattern) (formula : Formula 0) : String :=
  answerSummary (askFound RelationEnv.empty aliased 2 formula term 1 2)


/-- **The rows of the grid modulo `A = B`**: a term, a formula, the expected answer given the canonical forms, and
without them. -/
def aliasRows : List (Pattern × Formula 0 × String × String) := [
  -- `A`
  ((constant "A"), steps, "P canonical", "open"),
  ((constant "A"), reachesC, "P canonical", "open"),
  ((constant "A"), twoSteps, "R canonical", "open"),
  ((constant "A"), isB, "P canonical", "open"),
  ((constant "A"), isNotC, "P canonical", "open"),
  ((constant "A"), oneResult, "P canonical", "open"),
  -- `B`
  ((constant "B"), steps, "P exploration", "P exploration"),
  ((constant "B"), reachesC, "P exploration", "P exploration"),
  ((constant "B"), twoSteps, "R canonical", "open"),
  ((constant "B"), isB, "P exploration", "P exploration"),
  ((constant "B"), isNotC, "P canonical", "open"),
  ((constant "B"), oneResult, "P canonical", "open"),
  -- `C`
  ((constant "C"), steps, "R canonical", "open"),
  ((constant "C"), reachesC, "R canonical", "open"),
  ((constant "C"), twoSteps, "R canonical", "open"),
  ((constant "C"), isB, "R canonical", "open"),
  ((constant "C"), isNotC, "R exploration", "R exploration"),
  ((constant "C"), oneResult, "R canonical", "open")]

#guard aliasRows.all fun (term, formula, modulo, asWritten) =>
  summaryModulo term formula == modulo && summaryAsWritten term formula == asWritten

/-! ## Modulo an equation with a metavariable -/

namespace Unwrap

open Mettapedia.OSLF.NativeTypes.GeneratedLogic.CanonicalUnwrapControls
  (wrapped wrapForms start wrap pair reachesOk)

/-- `Pair (Wrap Ok) Err`. -/
def pairTerm : Pattern := pair (wrap CanonicalUnwrapControls.ok) CanonicalUnwrapControls.err

/-- `Wrap Ok`. -/
def wrappedOk : Pattern := wrap CanonicalUnwrapControls.ok

/-- Some step. -/
def stepsOnce : Formula 0 := CanonicalUnwrapControls.steps

/-- Two steps in a row. -/
def twoSteps : Formula 0 := .possibly .any stepsOnce

/-- Exactly one result. -/
def exactlyOneResult : Formula 0 := CanonicalUnwrapControls.oneResult

/-- The row's answer given the canonical forms: premise fuel two, two rounds. -/
def summaryModulo (term : Pattern) (formula : Formula 0) : String :=
  answerSummary (askFound RelationEnv.empty wrapped 2 formula term 1 2 (some wrapForms))

/-- The row's answer without them. -/
def summaryAsWritten (term : Pattern) (formula : Formula 0) : String :=
  answerSummary (askFound RelationEnv.empty wrapped 2 formula term 1 2)


/-- **The rows of the grid modulo `Wrap x = x`**: a term, a formula, the expected answer given the canonical forms,
and without them. -/
def unwrapRows : List (Pattern × Formula 0 × String × String) := [
  -- `Wrap (Pair (Wrap Ok) Err)`
  (start, stepsOnce, "P canonical", "open"),
  (start, reachesOk, "P canonical", "open"),
  (start, twoSteps, "R canonical", "open"),
  (start, exactlyOneResult, "P canonical", "open"),
  -- `Pair (Wrap Ok) Err`
  (pairTerm, stepsOnce, "P exploration", "P exploration"),
  (pairTerm, reachesOk, "P canonical", "open"),
  (pairTerm, twoSteps, "R canonical", "open"),
  (pairTerm, exactlyOneResult, "P canonical", "open"),
  -- `Wrap Ok`
  (wrappedOk, stepsOnce, "R canonical", "open"),
  (wrappedOk, reachesOk, "R canonical", "open"),
  (wrappedOk, twoSteps, "R canonical", "open"),
  (wrappedOk, exactlyOneResult, "R canonical", "open")]

#guard unwrapRows.all fun (term, formula, modulo, asWritten) =>
  summaryModulo term formula == modulo && summaryAsWritten term formula == asWritten

end Unwrap

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.AcceptanceMatrix
