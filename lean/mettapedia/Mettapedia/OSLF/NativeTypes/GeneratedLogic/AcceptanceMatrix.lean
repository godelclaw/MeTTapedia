import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CountingControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.ClosedControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CanonicalRegionControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CanonicalUnwrapControls

/-!
# The acceptance matrix of the front door

Rows `ask L q budget` with their expected answers, for λ with full β, over seven terms and twelve
formulas. The terms are a value, a redex, a redex under a binder, two terms with two redexes each (one
result, two results), Ω, and a term that grows forever. The formulas cover steps, stuckness, reachability,
safety, termination, divergence, a ν over μ alternation, counting, a constructor former and a
singleton.

Each row reads an answer and the evidence that settled it:

- `P` or `R`: proved or refuted;
- `certificate`: a finite-model certificate, here the cells the finder produced, given as the hint;
- `exploration`: the region the term reaches;
- `closed`: a closed region;
- `canonical`: a closed canonical region, for a language with equations given canonical forms;
- `open`: no evidence within the budget.

Soundness of every row is `ask_proved` and `ask_refuted`. The rows check that the front door answers,
and with which evidence: premise fuel three and six rounds. The term under a binder needs more fuel for
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
open Mettapedia.OSLF.NativeTypes.Executable.FiniteModelControls (fullLambda lambdaSignature underBinder app lam ok err)
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.CertificateControls (safety reachesErr)
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.SearchControls (found runsEnd growing)
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.ClosedControls (runsForever okStaysReachable omegaTerm)
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.CountingControls
  (distinctResults atMostOne deterministic sameResult twoResults)

/-- The kind of evidence. -/
def evidenceKind : Evidence → String
  | .certificate _ => "certificate"
  | .exploration _ => "exploration"
  | .closedRegion _ => "closed"
  | .canonicalRegion _ => "canonical"

/-- An answer and the kind of evidence that settled it. -/
def answerSummary : Answer → String
  | .proved evidence => "P " ++ evidenceKind evidence
  | .refuted evidence => "R " ++ evidenceKind evidence
  | .unknown _ => "open"

/-- The row's answer: full β, premise fuel three, the finder's cells as the hint, six rounds. -/
def summary (term : Pattern) (formula : Formula 0) : String :=
  answerSummary (ask RelationEnv.empty lambdaSignature fullLambda 3 formula term (some found) 6)

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

/-! ### `ok` -/

#guard summary ok canStep = "R closed"
#guard summary ok stuck = "P closed"
#guard summary ok reachesErr = "R certificate"
#guard summary ok safety = "P certificate"
#guard summary ok runsEnd = "P closed"
#guard summary ok runsForever = "R closed"
#guard summary ok okStaysReachable = "P closed"
#guard summary ok (distinctResults 2) = "R closed"
#guard summary ok atMostOne = "P closed"
#guard summary ok deterministic = "R closed"
#guard summary ok builtApp = "R closed"
#guard summary ok isOk = "P exploration"

/-! ### `errAfterOne` -/

#guard summary errAfterOne canStep = "P exploration"
#guard summary errAfterOne stuck = "R exploration"
#guard summary errAfterOne reachesErr = "P exploration"
#guard summary errAfterOne safety = "R exploration"
#guard summary errAfterOne runsEnd = "P closed"
#guard summary errAfterOne runsForever = "R closed"
#guard summary errAfterOne okStaysReachable = "R closed"
#guard summary errAfterOne (distinctResults 2) = "R closed"
#guard summary errAfterOne atMostOne = "P closed"
#guard summary errAfterOne deterministic = "P closed"
#guard summary errAfterOne builtApp = "P closed"
#guard summary errAfterOne isOk = "R certificate"

/-! ### `underBinder` -/

#guard summary underBinderOk canStep = "P exploration"
#guard summary underBinderOk stuck = "R exploration"
#guard summary underBinderOk reachesErr = "R certificate"
#guard summary underBinderOk safety = "P certificate"
#guard summary underBinderOk runsEnd = "open"
#guard summary underBinderOk runsForever = "open"
#guard summary underBinderOk okStaysReachable = "open"
#guard summary underBinderOk (distinctResults 2) = "open"
#guard summary underBinderOk atMostOne = "open"
#guard summary underBinderOk deterministic = "open"
#guard summary underBinderOk builtApp = "open"
#guard summary underBinderOk isOk = "open"

/-! ### `sameResult` -/

#guard summary sameResult canStep = "P exploration"
#guard summary sameResult stuck = "R exploration"
#guard summary sameResult reachesErr = "R certificate"
#guard summary sameResult safety = "P certificate"
#guard summary sameResult runsEnd = "P closed"
#guard summary sameResult runsForever = "R closed"
#guard summary sameResult okStaysReachable = "P closed"
#guard summary sameResult (distinctResults 2) = "R closed"
#guard summary sameResult atMostOne = "P closed"
#guard summary sameResult deterministic = "P closed"
#guard summary sameResult builtApp = "P closed"
#guard summary sameResult isOk = "R closed"

/-! ### `twoResults` -/

#guard summary twoResults canStep = "P exploration"
#guard summary twoResults stuck = "R exploration"
#guard summary twoResults reachesErr = "R closed"
#guard summary twoResults safety = "P closed"
#guard summary twoResults runsEnd = "P closed"
#guard summary twoResults runsForever = "R closed"
#guard summary twoResults okStaysReachable = "P closed"
#guard summary twoResults (distinctResults 2) = "P closed"
#guard summary twoResults atMostOne = "R closed"
#guard summary twoResults deterministic = "R closed"
#guard summary twoResults builtApp = "P closed"
#guard summary twoResults isOk = "R certificate"

/-! ### `omega` -/

#guard summary omegaTerm canStep = "P exploration"
#guard summary omegaTerm stuck = "R exploration"
#guard summary omegaTerm reachesErr = "R certificate"
#guard summary omegaTerm safety = "P certificate"
#guard summary omegaTerm runsEnd = "R exploration"
#guard summary omegaTerm runsForever = "P exploration"
#guard summary omegaTerm okStaysReachable = "R closed"
#guard summary omegaTerm (distinctResults 2) = "R closed"
#guard summary omegaTerm atMostOne = "P closed"
#guard summary omegaTerm deterministic = "P closed"
#guard summary omegaTerm builtApp = "P closed"
#guard summary omegaTerm isOk = "R closed"

/-! ### `growing` -/

#guard summary growing canStep = "P exploration"
#guard summary growing stuck = "R exploration"
#guard summary growing reachesErr = "R certificate"
#guard summary growing safety = "P certificate"
#guard summary growing runsEnd = "open"
#guard summary growing runsForever = "open"
#guard summary growing okStaysReachable = "open"
#guard summary growing (distinctResults 2) = "open"
#guard summary growing atMostOne = "open"
#guard summary growing deterministic = "open"
#guard summary growing builtApp = "open"
#guard summary growing isOk = "open"

/-! ## Modulo an equation -/

open Mettapedia.OSLF.NativeTypes.GeneratedLogic.CanonicalRegionControls
  (aliased aliasSignature aliasForms constant steps reachesC twoSteps isB isNotC oneResult)

/-- The row's answer given the canonical forms: premise fuel two, two rounds. -/
def summaryModulo (term : Pattern) (formula : Formula 0) : String :=
  answerSummary (ask RelationEnv.empty aliasSignature aliased 2 formula term none 2 (some aliasForms))

/-- The row's answer without them. -/
def summaryAsWritten (term : Pattern) (formula : Formula 0) : String :=
  answerSummary (ask RelationEnv.empty aliasSignature aliased 2 formula term none 2)


/-! ### `A` -/

#guard summaryModulo (constant "A") steps = "P canonical"
#guard summaryAsWritten (constant "A") steps = "open"
#guard summaryModulo (constant "A") reachesC = "P canonical"
#guard summaryAsWritten (constant "A") reachesC = "open"
#guard summaryModulo (constant "A") twoSteps = "R canonical"
#guard summaryAsWritten (constant "A") twoSteps = "open"
#guard summaryModulo (constant "A") isB = "P canonical"
#guard summaryAsWritten (constant "A") isB = "open"
#guard summaryModulo (constant "A") isNotC = "P canonical"
#guard summaryAsWritten (constant "A") isNotC = "open"
#guard summaryModulo (constant "A") oneResult = "P canonical"
#guard summaryAsWritten (constant "A") oneResult = "open"

/-! ### `B` -/

#guard summaryModulo (constant "B") steps = "P exploration"
#guard summaryAsWritten (constant "B") steps = "P exploration"
#guard summaryModulo (constant "B") reachesC = "P exploration"
#guard summaryAsWritten (constant "B") reachesC = "P exploration"
#guard summaryModulo (constant "B") twoSteps = "R canonical"
#guard summaryAsWritten (constant "B") twoSteps = "open"
#guard summaryModulo (constant "B") isB = "P exploration"
#guard summaryAsWritten (constant "B") isB = "P exploration"
#guard summaryModulo (constant "B") isNotC = "P canonical"
#guard summaryAsWritten (constant "B") isNotC = "open"
#guard summaryModulo (constant "B") oneResult = "P canonical"
#guard summaryAsWritten (constant "B") oneResult = "open"

/-! ### `C` -/

#guard summaryModulo (constant "C") steps = "R canonical"
#guard summaryAsWritten (constant "C") steps = "open"
#guard summaryModulo (constant "C") reachesC = "R canonical"
#guard summaryAsWritten (constant "C") reachesC = "open"
#guard summaryModulo (constant "C") twoSteps = "R canonical"
#guard summaryAsWritten (constant "C") twoSteps = "open"
#guard summaryModulo (constant "C") isB = "R canonical"
#guard summaryAsWritten (constant "C") isB = "open"
#guard summaryModulo (constant "C") isNotC = "R exploration"
#guard summaryAsWritten (constant "C") isNotC = "R exploration"
#guard summaryModulo (constant "C") oneResult = "R canonical"
#guard summaryAsWritten (constant "C") oneResult = "open"

/-! ## Modulo an equation with a metavariable -/

namespace Unwrap

open Mettapedia.OSLF.NativeTypes.GeneratedLogic.CanonicalUnwrapControls
  (wrapped wrapSignature wrapForms start wrap pair reachesOk)

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
  answerSummary (ask RelationEnv.empty wrapSignature wrapped 2 formula term none 2 (some wrapForms))

/-- The row's answer without them. -/
def summaryAsWritten (term : Pattern) (formula : Formula 0) : String :=
  answerSummary (ask RelationEnv.empty wrapSignature wrapped 2 formula term none 2)


/-! ### `Wrap (Pair (Wrap Ok) Err)` -/

#guard summaryModulo start stepsOnce = "P canonical"
#guard summaryAsWritten start stepsOnce = "open"
#guard summaryModulo start reachesOk = "P canonical"
#guard summaryAsWritten start reachesOk = "open"
#guard summaryModulo start twoSteps = "R canonical"
#guard summaryAsWritten start twoSteps = "open"
#guard summaryModulo start exactlyOneResult = "P canonical"
#guard summaryAsWritten start exactlyOneResult = "open"

/-! ### `Pair (Wrap Ok) Err` -/

#guard summaryModulo pairTerm stepsOnce = "P exploration"
#guard summaryAsWritten pairTerm stepsOnce = "P exploration"
#guard summaryModulo pairTerm reachesOk = "P canonical"
#guard summaryAsWritten pairTerm reachesOk = "open"
#guard summaryModulo pairTerm twoSteps = "R canonical"
#guard summaryAsWritten pairTerm twoSteps = "open"
#guard summaryModulo pairTerm exactlyOneResult = "P canonical"
#guard summaryAsWritten pairTerm exactlyOneResult = "open"

/-! ### `Wrap Ok` -/

#guard summaryModulo wrappedOk stepsOnce = "R canonical"
#guard summaryAsWritten wrappedOk stepsOnce = "open"
#guard summaryModulo wrappedOk reachesOk = "R canonical"
#guard summaryAsWritten wrappedOk reachesOk = "open"
#guard summaryModulo wrappedOk twoSteps = "R canonical"
#guard summaryAsWritten wrappedOk twoSteps = "open"
#guard summaryModulo wrappedOk exactlyOneResult = "R canonical"
#guard summaryAsWritten wrappedOk exactlyOneResult = "open"

end Unwrap

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.AcceptanceMatrix
