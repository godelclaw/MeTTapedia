import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Substitution
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SearchControls

/-!
# Controls: closing a formula with a free atom

"Some run reaches the atom" is `μX. a ∨ ◇X`, with the atom `a` free (`reachesAtom`). Substituting `Err`
for the atom gives the closed formula "some run reaches `Err`", syntactically (`closed_is_reachesErr`), and
its truth is that of the open formula with the atom read as the terms that are `Err` (`sat_close`).

- **Positive**: at `(λx. Err) ok` the open formula holds with the atom read as `Err`
  (`reaches_atom_err`).
- **Negative**: at `(λx. (λy. y) x) ok` it does not (`not_reaches_atom_err`).
- **Unfolding**: "some run reaches `Err`" unfolds to "`Err`, or some step to a term from which some run
  reaches `Err`" (`reachesErr_unfolds`), so `Err` itself reaches `Err` (`err_reaches_err`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.SubstitutionControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.NativeTypes.Executable.FiniteModelControls (underBinder app lam ok err)
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.CertificateControls (FullLambda reachesErr full_beta_never_errs)
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.SearchControls (err_proved)

/-- Some run reaches the atom, the free variable `0`. -/
def reachesAtom : Formula 1 := .mu (.or (.var 1) (.possibly .any (.var 0)))

/-- The atom read as `Err`. -/
def errAtom : Fin 1 → Formula 0 := fun _ => .is err

/-- **Substituting `Err` for the atom gives "some run reaches `Err`".** -/
theorem closed_is_reachesErr : reachesAtom.subst errAtom = reachesErr := rfl

/-- **The open formula holds at `(λx. Err) ok`** with the atom read as the terms that are `Err`. -/
theorem reaches_atom_err :
    FullLambda.sat (fun index => {other | FullLambda.sat Env.closed (errAtom index) other}) reachesAtom (app (lam err) ok) :=
  (FullLambda.sat_close errAtom reachesAtom _).mp (closed_is_reachesErr ▸ err_proved)

/-- **And fails at `(λx. (λy. y) x) ok`.** -/
theorem not_reaches_atom_err :
    ¬ FullLambda.sat (fun index => {other | FullLambda.sat Env.closed (errAtom index) other}) reachesAtom
      (app underBinder ok) := fun holds =>
  full_beta_never_errs (closed_is_reachesErr ▸ (FullLambda.sat_close errAtom reachesAtom _).mpr holds)

/-- **"Some run reaches `Err`" unfolds** to `Err` or a step to a term that reaches it. -/
theorem reachesErr_unfolds (term : Pattern) :
    FullLambda.sat Env.closed reachesErr term ↔
      FullLambda.sat Env.closed (.or (.is err) (.possibly .any reachesErr)) term :=
  FullLambda.sat_mu_unfold _ Env.closed term

/-- **`Err` reaches `Err`**, by the first disjunct of the unfolding. -/
theorem err_reaches_err : FullLambda.sat Env.closed reachesErr err :=
  (reachesErr_unfolds err).mpr (Or.inl ⟨rfl, Relation.EqvGen.refl _⟩)

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.SubstitutionControls
