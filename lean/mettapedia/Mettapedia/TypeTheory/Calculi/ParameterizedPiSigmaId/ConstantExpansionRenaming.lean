import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.ConstantExpansion
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.ConstantRenaming

/-! # Closed constant expansion under a bijective change of declaration names -/

set_option autoImplicit false
namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.ConstantExpansion
variable {Head : Type}

def renameBodies (names : DeclName ≃ DeclName) (bodies : Bodies Head) : Bodies Head :=
  fun actual => (bodies (names.symm actual)).mapConst names

theorem expand_mapConst (names : DeclName ≃ DeclName) (bodies : Bodies Head)
    {n : Nat} (term : Tm Head n) :
    expand (renameBodies names bodies) (term.mapConst names) =
      (expand bodies term).mapConst names := by
  induction term <;> simp_all only [expand, Tm.mapConst, renameBodies,
    Equiv.symm_apply_apply, Tm.mapConst_liftClosed]

#print axioms expand_mapConst
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.ConstantExpansion
