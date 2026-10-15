import Mettapedia.OSLF.Syntax.ScopedBindingFactors

/-!
# Complete raw factors through capture-avoiding substitution

An old factor maps to an actual factor of the substituted term. The
inherited hole-variable substitution and whole path are computed by the
existing binder-context operation. This preservation theorem does not
assert that substitution creates no additional constructor positions.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ScopedEncoding

variable {S : Binding.Signature}

def BindingFactor.substitute {target : Scope S} (factor : BindingFactor S target)
    (destination : Binding.Ctx S) (sigma : Binding.Sub S target.1 destination) :
    BindingFactor S (destination, target.2) where
  source := ((substituteContext factor.path destination sigma).holeContext, factor.source.2)
  value := Binding.bind (substituteContext factor.path destination sigma).holeVariables factor.value
  path := (substituteContext factor.path destination sigma).path

theorem BindingFactor.substitute_fill {target : Scope S} (factor : BindingFactor S target)
    (destination : Binding.Ctx S) (sigma : Binding.Sub S target.1 destination) :
    (factor.substitute destination sigma).fill = Binding.bind sigma factor.fill :=
  (substituteContext_fill factor.path destination sigma factor.value).symm

theorem bindingFactors_substitution_preserves {target : Scope S}
    (term : Binding.Term S target.1 target.2) (factor : BindingFactor S target)
    (member : factor ∈ bindingFactors term)
    (destination : Binding.Ctx S) (sigma : Binding.Sub S target.1 destination) :
    factor.substitute destination sigma ∈ bindingFactors (Binding.bind sigma term) := by
  apply (mem_bindingFactors_iff _ _).mpr
  exact (factor.substitute_fill destination sigma).trans
    (congrArg (Binding.bind sigma) (bindingFactors_sound term factor member))

theorem bindingFactors_substituted_image_subset {target : Scope S}
    (term : Binding.Term S target.1 target.2)
    (destination : Binding.Ctx S) (sigma : Binding.Sub S target.1 destination) :
    (bindingFactors term).map (fun factor => factor.substitute destination sigma) ⊆
      bindingFactors (Binding.bind sigma term) := by
  intro factor member
  obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
  exact bindingFactors_substitution_preserves term old oldMember destination sigma

end Mettapedia.OSLF.Binding.ScopedEncoding
