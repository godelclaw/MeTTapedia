import Mettapedia.Logic.HOL.Syntax.Subst

/-!
# Binder names over an intrinsic HOL context

Names decorate already scoped variables. Extending that decoration commutes
with a typed renaming. Concrete exporters still establish freshness of the
names they choose; this interface supplies no theorem authority.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL

universe u
variable {Base : Type u}

abbrev Names (context : Ctx Base) := ∀ {type}, Var context type → String

def Names.lift {context : Ctx Base} {domain : Ty Base}
    (fresh : String) (names : Names context) : Names (domain :: context)
  | _, .vz => fresh
  | _, .vs index => names index

theorem Names.lift_comp {source target : Ctx Base} {domain : Ty Base}
    (fresh : String) (names : Names target) (ρ : Rename Base source target) :
    (Names.lift (domain := domain) fresh (fun index => names (ρ index)) :
        Names (domain :: source)) =
      fun {type} (index : Var (domain :: source) type) =>
        Names.lift fresh names (Rename.lift ρ index) := by
  funext type index
  cases index <;> rfl

end Mettapedia.Logic.HOL
