import Mettapedia.GSLT.Core.GSLT

/-!
# Step-free GSLTs

A carrier with equality as its equations and no reductions is the GSLT of a
static fragment.  Observational theories read such a GSLT only through
contexts and observations, so its relative equivalences are purely
contextual.  Static fragments recur throughout observer theories, finite
automata and context-monoid presentations; this module gives them one
constructor.
-/

set_option autoImplicit false
set_option linter.dupNamespace false

namespace Mettapedia.GSLT

universe u

namespace GSLT

/-- A static equational carrier. Its existing equations are retained exactly;
no reduction is added. -/
abbrev equationOnly (Term : Type u) (equations : Setoid Term) : GSLT.{u} where
  Term := Term
  equations := equations
  rewrites _ _ := False
  rewrites_resp_left := fun _ impossible => impossible.elim
  rewrites_resp_right := fun impossible _ => impossible.elim

/-- The GSLT on `Term` whose equations are equality and which has no
reductions. -/
abbrev stepFree (Term : Type u) : GSLT.{u} :=
  equationOnly Term ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩

theorem equationOnly_not_step (Term : Type u) (equations : Setoid Term) (source target : Term) :
    ¬ (equationOnly Term equations).Step source target := fun impossible => impossible

theorem equationOnly_equiv_iff (Term : Type u) (equations : Setoid Term) (left right : Term) :
    (equationOnly Term equations).Equiv left right ↔ equations.r left right := Iff.rfl

/-- A step-free GSLT has no steps. -/
theorem stepFree_not_step (Term : Type u) (source target : Term) :
    ¬ (stepFree Term).Step source target :=
  fun impossible => impossible

/-- Its equations are equality. -/
theorem stepFree_equiv_iff (Term : Type u) (left right : Term) :
    (stepFree Term).Equiv left right ↔ left = right :=
  Iff.rfl

end GSLT

end Mettapedia.GSLT
