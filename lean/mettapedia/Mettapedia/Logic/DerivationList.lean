import Mettapedia.Logic.Derivation

/-!
# Ordered child lists for finite derivation nodes

This is the existing finite derivation datatype with list-based construction.
Replay still checks the supplied local witness and every child occurrence in
order. The constructor does not identify repeated or equal conclusions.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.Derivation

universe u v
variable {J : Type u} {W : Type v}

def fromChildren (conclusion : J) (witness : W) (children : List (Derivation J W)) : Derivation J W :=
  .node conclusion witness children.length children.get

@[simp] theorem concl_fromChildren (conclusion : J) (witness : W) (children : List (Derivation J W)) :
    (fromChildren conclusion witness children).concl = conclusion := rfl

theorem valid_fromChildren {rules : List J → J → Prop} (interface : RuleWitness.{u, v} rules)
    (conclusion : J) (witness : interface.W) (children : List (Derivation J interface.W)) :
    (fromChildren conclusion witness children).valid interface =
      (interface.isInstance witness (children.map concl) conclusion &&
        (children.map (valid interface)).all id) := by
  simp only [fromChildren, valid, List.get_eq_getElem, List.ofFn_getElem_eq_map]

end Mettapedia.Logic.Derivation
