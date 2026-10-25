import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Verdicts
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SearchControls

/-!
# Controls: one verdict type

Answers of different strategies, read through one verdict type.

- `ask` proves that `(λx. (λy. y) x) ok` is safe under full β: an established verdict (`ask_established`).
- A finite-model certificate refutes that the same term reaches `Err` under root β: a refuted verdict
  (`certificate_refutes`), carrying the proof of the negation (`certificate_refutation_holds`).
- A proof-carrying outcome reads the same before and after (`outcome_read`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.VerdictControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.Verdicts
open Mettapedia.OSLF.NativeTypes.Executable.FiniteModelControls
  (fullLambda lambdaSignature lambdaCalculus cleanCertificate isDirty twice underBinder app ok err)
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.CertificateControls (safety)
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.SearchControls (found)
open Mettapedia.OSLF.NativeTypes.Decision.Reference.Core (Outcome)

/-- **`ask`'s proof, as an established verdict.** -/
theorem ask_established :
    (ofAsk RelationEnv.empty lambdaSignature fullLambda 2 safety (app underBinder ok) (some found) 0).answer = some true := by
  decide +kernel

/-- **A certificate's refutation, as a refuted verdict.** -/
theorem certificate_refutes : (ofCannotReach cleanCertificate lambdaCalculus [err] isDirty twice).answer = some false := by
  decide +kernel

/-- The refuted verdict carries the negation. -/
theorem certificate_refutation_holds :
    ¬ Mettapedia.OSLF.Framework.BackwardSearch.Reaches
      (Mettapedia.OSLF.Framework.BackwardSearch.between
        (Mettapedia.OSLF.Framework.HerbrandBridge.languageSpan lambdaCalculus)
        Mettapedia.OSLF.Framework.FiniteModels.ObjectState)
      (Mettapedia.OSLF.Framework.HerbrandBridge.Goal [err]) twice :=
  Verdict.fails_of_answer certificate_refutes

/-- **An outcome reads the same.** -/
theorem outcome_read : (ofOutcome (Outcome.proved (show 2 + 2 = 4 from rfl))).answer = some true := rfl

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.VerdictControls
