import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Completeness
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CountingControls

/-!
# Controls: a complete front door on a finite region

Under full β, `(λx. ok) ((λy. y) Err)` reaches finitely many terms, and premise fuel three lists every
state's steps. Its closure under steps and parts has ten terms (`closure_two_results`), so `ask` decides
every forward formula about it within ten rounds, whatever the formula (`two_results_decided`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.CompletenessControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.NativeTypes.Executable.FiniteModelControls (fullLambda lambdaSignature)
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.CountingControls (twoResults)

/-- The terms `(λx. ok) ((λy. y) Err)` reaches, with their parts. -/
def closureOfTwoResults : List Pattern := grow RelationEnv.empty fullLambda 3 twoResults 4

theorem closure_length : closureOfTwoResults.length = 10 := by decide +kernel

/-- **A finite closure, completely listed.** -/
theorem closure_two_results : Closure RelationEnv.empty fullLambda 3 twoResults closureOfTwoResults := by
  constructor <;> decide +kernel

/-- **Every forward formula about it is decided** in ten rounds. -/
theorem two_results_decided (formula : Formula 0) (forward : formula.forward = true)
    (hint : Option CertificateCandidate) :
    ∃ evidence, ask RelationEnv.empty lambdaSignature fullLambda 3 formula twoResults hint 10 = .proved evidence ∨
      ask RelationEnv.empty lambdaSignature fullLambda 3 formula twoResults hint 10 = .refuted evidence :=
  ask_decides (by decide) closure_two_results forward (by rw [closure_length]) hint

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.CompletenessControls
