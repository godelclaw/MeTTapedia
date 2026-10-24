import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Certificates
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Controls
import Mettapedia.OSLF.NativeTypes.Executable.ContextualControls

/-!
# Controls: finite-model certificates for generated formulas

λ with full β, which reduces under binders through authored congruences, and the two-value cleanliness
certificate: a term is clean when it cannot produce `Err`.

- **Safety, proved.** At `(λx. (λy. y) x) ok` the certificate proves `νX. ¬Err ∧ □X`: no run reaches
  `Err` (`full_beta_safe`).
- **Reaching `Err`, refuted.** It refutes `μX. Err ∨ ◇X` there (`full_beta_never_errs`), which is the
  same verdict read through the dual.
- **Infinitely many states.** `(λx. x x x) (λx. x x x)` grows at every step and never stops
  (`growing_steps`). The same finite check proves it safe (`growing_safe`).
- **Silence where it must be.** `(λx. Err) ok` reaches `Err` (`err_reachable`), and the certificate claims
  nothing there (`silent_at_err`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.CertificateControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep
open Mettapedia.OSLF.NativeTypes.Executable.FiniteModelControls (fullLambda cleanCertificate underBinder app lam ok err)
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.Controls (step_of_listed)

abbrev FullLambda : NativeStructure Pattern := referenceStructure RelationEnv.empty fullLambda

/-- No run reaches `Err`. -/
def safety : Formula 0 := .nu (.and (.isNot err) (.necessarily .any (.var 0)))

/-- Some run reaches `Err`. -/
def reachesErr : Formula 0 := .mu (.or (.is err) (.possibly .any (.var 0)))

/-- **The certificate proves safety** at `(λx. (λy. y) x) ok`. -/
theorem full_beta_safe : FullLambda.sat Env.closed safety (app underBinder ok) :=
  proves_sound (certificate := cleanCertificate) (by decide +kernel)

/-- **The certificate refutes reaching `Err`** there. -/
theorem full_beta_never_errs : ¬ FullLambda.sat Env.closed reachesErr (app underBinder ok) :=
  refutes_sound (certificate := cleanCertificate) (by decide +kernel)

/-- `λx. x x x`. -/
def tripler : Pattern := lam (app (app (.bvar 0) (.bvar 0)) (.bvar 0))

/-- `(λx. x x x) (λx. x x x)`: every step adds a copy. -/
def growing : Pattern := app tripler tripler

/-- It steps, to a larger term. -/
theorem growing_steps : FullLambda.step growing .any (app growing tripler) :=
  step_of_listed (fuel := 1) (by decide) (by decide) (by decide +kernel)

/-- **The same finite check proves the growing term safe.** -/
theorem growing_safe : FullLambda.sat Env.closed safety growing :=
  proves_sound (certificate := cleanCertificate) (by decide +kernel)

/-- `(λx. Err) ok` reaches `Err` in one step. -/
theorem err_reachable : FullLambda.sat Env.closed reachesErr (app (lam err) ok) := by
  intro closed isClosed
  have errIn : err ∈ closed := isClosed err (Or.inl ⟨by decide, Relation.EqvGen.refl _⟩)
  exact isClosed _ (Or.inr ⟨err, step_of_listed (fuel := 1) (by decide) (by decide) (by decide +kernel), errIn⟩)

/-- The certificate claims nothing there. -/
theorem silent_at_err :
    proves cleanCertificate fullLambda safety (app (lam err) ok) = false ∧
      refutes cleanCertificate fullLambda reachesErr (app (lam err) ok) = false := by
  constructor <;> decide +kernel

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.CertificateControls
