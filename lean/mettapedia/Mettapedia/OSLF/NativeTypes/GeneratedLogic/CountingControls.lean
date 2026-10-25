import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SearchControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.HigherOrder

/-!
# Controls: counting results

λ with full β, reducing under binders and in arguments. Counting counts distinct results, as the
language identifies terms, so two steps to the same term count once.

- **Two redexes, one result.** `(λx. x) ((λy. y) ok)` steps at the root and inside the argument, and
  both steps give `(λx. x) ok`. It is deterministic (`same_result_deterministic`), and it does not have
  two distinct results (`same_result_not_two`).
- **Two results.** `(λx. ok) ((λy. y) Err)` steps to `ok` and to `(λx. ok) Err`. It has two distinct
  results (`two_results`), so it is not deterministic (`two_results_not_deterministic`).
- **At most one is a dual.** Determinism is `exactlyOne` (`deterministic_is_exactlyOne`). Dualizing the
  inner formula as well gives a formula that holds even with two results (`inner_dual_trivial`).
- **Every verdict is evidence.** Each answer is a closed region grown for four rounds with premise fuel
  three, which decides counting formulas exactly. The higher-order translation of "two distinct results"
  holds where the formula does (`two_results_translated`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.CountingControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.NativeTypes.Executable.FiniteModelControls (fullLambda lambdaSignature app lam ok err)
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.CertificateControls (FullLambda)

/-- At least `count` distinct results. -/
def distinctResults (count : ℕ) : Formula 0 := .atLeast count .forward .any .top

/-- At most one distinct result: fewer than two results fail `⊥`. -/
def atMostOne : Formula 0 := .allButFewer 2 .forward .any .bot

/-- Exactly one distinct result. -/
def deterministic : Formula 0 := .and (distinctResults 1) atMostOne

/-- `(λx. x) ((λy. y) ok)`: two redexes. -/
def sameResult : Pattern := app (lam (.bvar 0)) (app (lam (.bvar 0)) ok)

/-- `(λx. ok) ((λy. y) Err)`: two redexes with different results. -/
def twoResults : Pattern := app (lam ok) (app (lam (.bvar 0)) err)

theorem same_result_answer :
    ask RelationEnv.empty lambdaSignature fullLambda 3 deterministic sameResult none 4 = .proved (.closedRegion 4) := by
  decide +kernel

/-- **Two redexes, one result: deterministic.** -/
theorem same_result_deterministic : FullLambda.sat Env.closed deterministic sameResult :=
  ask_proved same_result_answer

theorem same_result_not_two_answer :
    ask RelationEnv.empty lambdaSignature fullLambda 3 (distinctResults 2) sameResult none 4 =
      .refuted (.closedRegion 4) := by
  decide +kernel

/-- **The two steps count once.** -/
theorem same_result_not_two : ¬ FullLambda.sat Env.closed (distinctResults 2) sameResult :=
  ask_refuted same_result_not_two_answer

theorem two_results_answer :
    ask RelationEnv.empty lambdaSignature fullLambda 3 (distinctResults 2) twoResults none 4 =
      .proved (.closedRegion 4) := by
  decide +kernel

/-- **Two distinct results.** -/
theorem two_results : FullLambda.sat Env.closed (distinctResults 2) twoResults :=
  ask_proved two_results_answer

theorem two_results_not_deterministic_answer :
    ask RelationEnv.empty lambdaSignature fullLambda 3 deterministic twoResults none 4 =
      .refuted (.closedRegion 4) := by
  decide +kernel

/-- **So it is not deterministic.** -/
theorem two_results_not_deterministic : ¬ FullLambda.sat Env.closed deterministic twoResults :=
  ask_refuted two_results_not_deterministic_answer

/-- The named combinator is the same formula. -/
theorem deterministic_is_exactlyOne : deterministic = Formula.exactlyOne .forward .any := rfl

/-- **Dualizing the inner formula as well says something else.** "Fewer than two results fail `⊤`" holds
even at the term with two results, since no result fails `⊤`. At most one result is the dual of at least
two satisfying `⊤`, not of at least two satisfying its dual. -/
theorem inner_dual_trivial :
    FullLambda.sat Env.closed (Formula.dual (.atLeast 2 .forward .any (Formula.dual .top))) twoResults := by
  rintro ⟨witnesses, length, -, all⟩
  match witnesses, length with
  | witness :: _, _ => exact (all witness List.mem_cons_self).2 trivial

open Mettapedia.OSLF.Framework.NativeBasis (nowhere)
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.HigherOrder (standardModel presentation translate denote_translate_closed)

/-- **The translation of "two distinct results" holds there too.** -/
theorem two_results_translated :
    ((standardModel FullLambda).denote (translate (distinctResults 2)) (nowhere (presentation FullLambda))
      (ULift.up twoResults)).down :=
  (denote_translate_closed (distinctResults 2) _).mpr two_results

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.CountingControls
