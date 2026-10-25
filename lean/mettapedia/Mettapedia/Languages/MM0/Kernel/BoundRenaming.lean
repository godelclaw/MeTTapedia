import Mettapedia.Languages.MM0.Kernel.AdmissibleSubstitution

/-!
# Independence of bound names under variable renaming

For two bound formals, a sort-correct variable substitution is admissible
exactly when its two target names differ. This is a property of context
positions. It imposes no inequality on values assigned to those positions by
an interpretation.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.MM0.Kernel.Substitution

/-- The independence test adds precisely name inequality to the typing of
this two-bound-variable substitution, in an arbitrary target context. -/
theorem two_bound_check_iff (signature : TermSignature) (target : Context)
    (sort left right : Nat)
    (leftBound : target[left]? = some (.bound sort))
    (rightBound : target[right]? = some (.bound sort)) :
    checkAdmissible signature [.bound sort, .bound sort] target
      [.var left, .var right] = true ↔ left ≠ right := by
  simp [checkAdmissible, checkArguments, Preterm.checkBinder, Preterm.boundSort?, leftBound, rightBound,
    entries, checkRow, checkPair, Binder.DependsOn, Preterm.support?, ne_comm]

/-- The declarative and executable boundaries agree at the original MM0
substitution interface. -/
theorem two_bound_admissible_iff (signature : TermSignature) (target : Context)
    (sort left right : Nat)
    (leftBound : target[left]? = some (.bound sort))
    (rightBound : target[right]? = some (.bound sort)) :
    Admissible signature [.bound sort, .bound sort] target
      [.var left, .var right] ↔ left ≠ right := by
  rw [← checkAdmissible_iff, two_bound_check_iff signature target sort left right leftBound rightBound]

end Mettapedia.Languages.MM0.Kernel.Substitution
