import Mettapedia.TypeTheory.IndexedPolynomialSubstitution

/-!
# Parameter-substitution controls for dependent polynomial induction

Constructor payloads and the result fibre both depend on the natural-number
base. The base substitution is parity: it is nonconstant and identifies 0
with 2. The comparisons therefore exercise a genuine parameter change rather
than an identity substitution on a constant family.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.IndexedPolynomial.SubstitutionControls

/-- At base `bound`, each list element lies in `Fin (bound + 1)`. -/
def boundedLists : IndexedPolynomial Nat (fun _ => Unit) where
  Shape := fun bound _ => ListExample.Shape (Fin (bound + 1))
  Position := fun shape => match shape with
    | .nil => Empty
    | .cons _ => Unit
  next := fun _ _ => ()

/-- The dependent result is a sum modulo the base's positive modulus. -/
def sumModulo : Algebra.Displayed (Algebra.initial boundedLists)
    (fun bound _ _ => Fin (bound + 1)) where
  act := by
    intro bound index shape children hypotheses
    cases shape with
    | nil => exact ⟨0, Nat.zero_lt_succ bound⟩
    | cons head =>
        exact ⟨(head.val + (hypotheses ()).val) % (bound + 1),
          Nat.mod_lt _ (Nat.zero_lt_succ bound)⟩

def parityBase (input : Nat) : Nat := input % 2

theorem parityBase_nonconstant : parityBase 0 ≠ parityBase 1 := by decide

theorem parityBase_not_injective : ¬ Function.Injective parityBase := by
  intro injective
  have impossible : (0 : Nat) = 2 := injective (by decide)
  exact (by decide : (0 : Nat) ≠ 2) impossible

/-- A constructor whose payload type is selected by the substituted base. -/
def singleton (base : Nat) : Fix (boundedLists.reindex parityBase) base () :=
  .roll (.cons ⟨parityBase base, Nat.lt_succ_self _⟩)
    (fun _ => .roll .nil (fun impossible => nomatch impossible))

/-- Both result fibres and constructor payloads are transported by the shared
substitution theorem. -/
theorem elimination_commutes (base : Nat)
    (tree : Fix (boundedLists.reindex parityBase) base ()) :
    sumModulo.initialSection.toFun (parityBase base) ()
        (Fix.reindexTo boundedLists parityBase tree) =
      (sumModulo.reindex parityBase).initialSection.toFun base () tree :=
  Algebra.Displayed.reindex_initialSection sumModulo parityBase base () tree

theorem even_result :
    (sumModulo.reindex parityBase).initialSection.toFun 2 () (singleton 2) =
      (⟨0, by decide⟩ : Fin (parityBase 2 + 1)) := rfl

theorem odd_result :
    (sumModulo.reindex parityBase).initialSection.toFun 3 () (singleton 3) =
      (⟨1, by decide⟩ : Fin (parityBase 3 + 1)) := rfl

/-- Equal substituted parameters may come from distinct source contexts. -/
theorem merged_contexts_same_result :
    ((sumModulo.reindex parityBase).initialSection.toFun 0 () (singleton 0)).val =
      ((sumModulo.reindex parityBase).initialSection.toFun 2 () (singleton 2)).val := rfl

/-- A nonconstant substitution does not collapse all dependent observations. -/
theorem different_parameters_distinguished :
    ((sumModulo.reindex parityBase).initialSection.toFun 2 () (singleton 2)).val ≠
      ((sumModulo.reindex parityBase).initialSection.toFun 3 () (singleton 3)).val := by
  exact Nat.zero_ne_one

#print axioms elimination_commutes
#print axioms parityBase_not_injective
#print axioms even_result
#print axioms odd_result
#print axioms merged_contexts_same_result
#print axioms different_parameters_distinguished

end Mettapedia.TypeTheory.IndexedPolynomial.SubstitutionControls
