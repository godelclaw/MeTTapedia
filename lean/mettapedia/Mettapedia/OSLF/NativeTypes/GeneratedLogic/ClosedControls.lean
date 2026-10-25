import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SearchControls

/-!
# Controls: closed regions

λ with full β, reducing under binders.

- **Every run ends.** From `(λx. (λy. y) x) ok` every run ends (`runs_end`): a universal least fixed
  point, which no certificate proves, since a certificate's steps form a preorder.
- **Forward alternation.** From every term `(λx. (λy. y) x) ok` reaches, `ok` is still reachable
  (`ok_stays_reachable`): a greatest fixed point over a least one, ∀ over ∃.
- **Ω.** `(λx. x x) (λx. x x)` runs forever (`omega_runs_forever`), and not every run of it ends
  (`omega_does_not_end`). The exploration settles both first, the second through the dual. Ω's region
  also closes, since Ω steps to itself, and decides both (`omega_closed`).
- **Not every region closes.** The growing term's region does not close in four rounds
  (`growing_unclosed`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.ClosedControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.NativeTypes.Executable.FiniteModelControls (fullLambda lambdaSignature underBinder app lam ok)
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.CertificateControls (FullLambda)
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.SearchControls (runsEnd growing)

/-- Some run is infinite. -/
def runsForever : Formula 0 := .nu (.possibly .any (.var 0))

/-- From every reachable term, `ok` is reachable. -/
def okStaysReachable : Formula 0 :=
  .nu (.and (.mu (.or (.is ok) (.possibly .any (.var 0)))) (.necessarily .any (.var 0)))

def omegaHalf : Pattern := lam (app (.bvar 0) (.bvar 0))

/-- `(λx. x x) (λx. x x)`. -/
def omegaTerm : Pattern := app omegaHalf omegaHalf

theorem runs_end_answer :
    ask RelationEnv.empty lambdaSignature fullLambda 5 runsEnd (app underBinder ok) none 6 = .proved (.closedRegion 6) := by
  decide +kernel

/-- **Every run of `(λx. (λy. y) x) ok` ends.** -/
theorem runs_end : FullLambda.sat Env.closed runsEnd (app underBinder ok) := ask_proved runs_end_answer

theorem ok_stays_reachable_answer :
    ask RelationEnv.empty lambdaSignature fullLambda 5 okStaysReachable (app underBinder ok) none 6 =
      .proved (.closedRegion 6) := by
  decide +kernel

/-- **From every term it reaches, `ok` is still reachable.** -/
theorem ok_stays_reachable : FullLambda.sat Env.closed okStaysReachable (app underBinder ok) :=
  ask_proved ok_stays_reachable_answer

theorem omega_forever_answer :
    ask RelationEnv.empty lambdaSignature fullLambda 5 runsForever omegaTerm none 6 = .proved (.exploration 6) := by
  decide +kernel

/-- **Ω runs forever.** -/
theorem omega_runs_forever : FullLambda.sat Env.closed runsForever omegaTerm :=
  ask_proved omega_forever_answer

theorem omega_end_answer :
    ask RelationEnv.empty lambdaSignature fullLambda 5 runsEnd omegaTerm none 6 = .refuted (.exploration 6) := by
  decide +kernel

/-- **Not every run of Ω ends.** -/
theorem omega_does_not_end : ¬ FullLambda.sat Env.closed runsEnd omegaTerm :=
  ask_refuted omega_end_answer

/-- **Ω's region closes** and decides both formulas there too. -/
theorem omega_closed :
    decideFrom RelationEnv.empty fullLambda 5 runsForever omegaTerm 6 = some true ∧
      decideFrom RelationEnv.empty fullLambda 5 runsEnd omegaTerm 6 = some false := by
  constructor <;> decide +kernel

/-- The growing term's region does not close in four rounds. -/
theorem growing_unclosed : decideFrom RelationEnv.empty fullLambda 5 runsEnd growing 4 = none := by
  decide +kernel

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.ClosedControls
