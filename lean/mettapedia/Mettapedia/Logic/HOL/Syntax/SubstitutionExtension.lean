import Mettapedia.Logic.HOL.Syntax.Subst

/-!
# Extending typed simultaneous substitutions

A substitution into an extended source context consists of the image of its
new variable and the old substitution. Instantiating a lifted substitution is
exactly this extension, including below further binders.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL

universe u v
variable {Base : Type u} {Const : Ty Base → Type v}
variable {gamma delta : Ctx Base} {domain result : Ty Base}

def Subst.cons (head : Term Const delta domain) (tail : Subst Const gamma delta) :
    Subst Const (domain :: gamma) delta
  | _, .vz => head
  | _, .vs index => tail index

theorem instantiate_subst_lift (argument : Term Const delta domain)
    (theta : Subst Const gamma delta) (body : Term Const (domain :: gamma) result) :
    instantiate argument (subst (Subst.lift theta) body) = subst (Subst.cons argument theta) body := by
  rw [instantiate, subst_comp]
  apply subst_ext
  intro type index
  cases index with
  | vz => rfl
  | vs index =>
      change instantiate argument (weaken (theta index)) = theta index
      exact instantiate_weaken argument (theta index)

#print axioms instantiate_subst_lift

end Mettapedia.Logic.HOL
