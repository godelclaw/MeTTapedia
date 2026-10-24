import Mettapedia.Languages.MM0.Kernel.AdmissibleSubstitution

/-!
# Constructing substitutions for regular MM0 formal parameters

A list of sorted argument expressions instantiates the corresponding regular
formal context. No independence rows arise without bound formals. This
construction permits different sorts at the different argument positions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Kernel.Substitution

theorem admissible_regular {signature : TermSignature} {target : Context}
    {expressions : List Preterm} {sorts : List Nat}
    (typed : List.Forall₂ (fun expression sort =>
      Preterm.HasType signature target expression [] sort) expressions sorts) :
    Admissible signature (sorts.map (fun sort => .regular sort ∅)) target expressions := by
  apply (admissible_iff_typed_of_regular_formals _ _ _ _ ?_).mpr
  · induction typed with
    | nil => exact .nil
    | cons head _ ih => exact .cons (.regular head) ih
  · intro binder member
    obtain ⟨sort, _, rfl⟩ := List.mem_map.mp member
    exact ⟨sort, ∅, rfl⟩

#print axioms admissible_regular

end Mettapedia.Languages.MM0.Kernel.Substitution
