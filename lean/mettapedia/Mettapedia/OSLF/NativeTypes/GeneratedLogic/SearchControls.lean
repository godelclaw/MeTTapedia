import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Search
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CertificateControls

/-!
# Controls: asking, with evidence from both sides

**Levin search over codes**, on numbers written in unary: the search for a number whose square is `9`
finds `3` by round `13`, the bound Levin's theorem gives for a code of description length `10` and cost
`3` (`finds_three`). Nothing is found in `12` rounds (`not_in_twelve`). The open answer comes with its
grade: every checked number has a longer code or a higher cost (`twelve_rounds_bound`).

**Asking about full β under binders**, with the cells the finder produced as the hint:
- safety at `(λx. (λy. y) x) ok` is proved by the certificate, and reaching `Err` is refuted by it
  (`clean_proved`, `clean_refuted`);
- at `(λx. Err) ok`, reaching `Err` is proved by exploring two rounds, and safety is refuted by the same
  exploration (`err_proved`, `err_refuted`);
- that `ok` is stuck is proved by a closed region (`stuck_proved`);
- that every run of `(λx. x x x) (λx. x x x)` ends stays open (`growing_open`). Its region never closes,
  a certificate's steps form a preorder, and an exploration proves existential formulas only. The open
  answer bounds every certificate that would decide it (`growing_bound`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.SearchControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.NativeTypes.Executable.FiniteModelControls
  (fullLambda fullLambdaCells lambdaSignature underBinder app lam ok err)
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.CertificateControls (FullLambda safety reachesErr)

/-! ## Levin search over codes -/

/-- A number written in unary, using every bit. -/
def readNumber (bits : List Bool) : Option ℕ :=
  match CertificateCandidate.readUnary bits with
  | some (number, []) => some number
  | _ => none

def squareIsNine (number : ℕ) : Bool := number * number == 9

theorem finds_three : (explain readNumber id squareIsNine 13).map (·.1) = some 3 := by decide

theorem not_in_twelve : explain readNumber id squareIsNine 12 = none := by decide

/-- The code of `3`: description length `10`, so Levin's bound is round `10 + ⌈log₂ 3⌉ + 1 = 13`. -/
theorem three_within_bound :
    (explain readNumber id squareIsNine (Codes.codeLength (CertificateCandidate.unary 3) + Nat.clog 2 3 + 1)).isSome :=
  (explain_finds readNumber id squareIsNine (bits := CertificateCandidate.unary 3) (by decide) (by decide)).1

/-- **The open answer's grade**: every number that checks has `ℓ + ⌈log₂ t⌉ + 1 > 12` for each of its
codes. -/
theorem twelve_rounds_bound {bits : List Bool} {number : ℕ} (decoded : readNumber bits = some number)
    (checked : squareIsNine number = true) : 12 < Codes.codeLength bits + Nat.clog 2 number + 1 :=
  exhausted_bound readNumber id squareIsNine not_in_twelve decoded checked

/-! ## Asking about full β -/

/-- The cells the finder produced, as a candidate over two values. -/
def found : CertificateCandidate := ⟨1, 1, fullLambdaCells⟩

theorem fullLambda_free : fullLambda.isEquationFree = true := by decide

theorem clean_answer :
    ask RelationEnv.empty lambdaSignature fullLambda 2 safety (app underBinder ok) (some found) 0 =
      .proved (.certificate found) := by decide +kernel

/-- **Safety, proved by the certificate.** -/
theorem clean_proved : FullLambda.sat Env.closed safety (app underBinder ok) :=
  ask_proved clean_answer

theorem clean_refuted_answer :
    ask RelationEnv.empty lambdaSignature fullLambda 2 reachesErr (app underBinder ok) (some found) 0 =
      .refuted (.certificate found) := by decide +kernel

/-- **Reaching `Err`, refuted by the certificate.** -/
theorem clean_refuted : ¬ FullLambda.sat Env.closed reachesErr (app underBinder ok) :=
  ask_refuted clean_refuted_answer

theorem err_answer :
    ask RelationEnv.empty lambdaSignature fullLambda 2 reachesErr (app (lam err) ok) none 2 =
      .proved (.exploration 2) := by decide +kernel

/-- **Reaching `Err`, proved by exploration.** -/
theorem err_proved : FullLambda.sat Env.closed reachesErr (app (lam err) ok) :=
  ask_proved err_answer

theorem err_refuted_answer :
    ask RelationEnv.empty lambdaSignature fullLambda 2 safety (app (lam err) ok) none 2 =
      .refuted (.exploration 2) := by decide +kernel

/-- **Safety, refuted by the same exploration.** -/
theorem err_refuted : ¬ FullLambda.sat Env.closed safety (app (lam err) ok) :=
  ask_refuted err_refuted_answer

/-- **That `ok` is stuck is proved by a closed region**: `ok` has no step, and its region is itself. -/
theorem stuck_answer :
    ask RelationEnv.empty lambdaSignature fullLambda 2 (.necessarily .any .bot) ok (some found) 3 =
      .proved (.closedRegion 3) := by
  decide +kernel

theorem stuck_proved : FullLambda.sat Env.closed (.necessarily .any .bot) ok :=
  ask_proved stuck_answer

/-- `λx. x x x`. -/
def tripler : Pattern := lam (app (app (.bvar 0) (.bvar 0)) (.bvar 0))

/-- `(λx. x x x) (λx. x x x)`: every step adds a copy. -/
def growing : Pattern := app tripler tripler

/-- Every run ends. -/
def runsEnd : Formula 0 := .mu (.necessarily .any (.var 0))

/-- **An open answer**: that every run of the growing term ends stays open after four rounds. Its region
never closes, a certificate's steps form a preorder, and an exploration proves existential formulas
only. -/
theorem growing_open : ask RelationEnv.empty lambdaSignature fullLambda 2 runsEnd growing none 4 = .unknown 4 := by
  decide +kernel

/-- The open answer bounds every certificate that would decide it. -/
theorem growing_bound (candidate : CertificateCandidate)
    (decides : provesBy lambdaSignature fullLambda runsEnd growing candidate = true ∨
      refutesBy lambdaSignature fullLambda runsEnd growing candidate = true) :
    4 < Codes.codeLength candidate.encode + Nat.clog 2 candidate.cost + 1 :=
  ask_open growing_open candidate decides

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.SearchControls
