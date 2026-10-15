import Mettapedia.OSLF.Syntax.BindingGroundedPredicates
import Mettapedia.OSLF.Syntax.BindingPredicateBooleanGuard

/-!
# Complete Boolean guards on retained closed origins

The decision uses the independently supplied predicate at the closed
origin. Both Boolean fibres are compared with the actual native predicate
and its Heyting negation pulled back along the grounding map. The guard is
not extended to all open programs.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.BindingClosedPredicateGuard

open _root_.CategoryTheory BindingConstructorPredicates IntrinsicScopedConditionalPresheaf
open BindingGroundedPredicates BindingPredicateBooleanGuard

universe u
variable {S : Signature} {A : BindingCloneAlgebra.Algebra.{u} S} {sort : S.Srt}

def trueValues : Subfunctor (booleans (A := A)) where
  obj _ := {value | value.down = true}
  map := by intro first last change value member; exact member

def falseValues : Subfunctor (booleans (A := A)) where
  obj _ := {value | value.down = false}
  map := by intro first last change value member; exact member

variable (predicate : Predicate A sort)
variable [DecidablePred (predicate.holds (Γ := []))]

def guard : closedPrograms (A := A) (sort := sort) ⟶ booleans (A := A) where
  app _ := TypeCat.ofHom fun (value : A.substitution.Carrier [] sort) =>
    ⟨decide (predicate.holds (Γ := []) value)⟩
  naturality _ _ _ := rfl

theorem guard_true (value : A.substitution.Carrier [] sort) (world : Base A) :
    (guard predicate |>.app world value).down = true ↔ predicate.holds value := by
  change decide (predicate.holds value) = true ↔ _
  simp only [decide_eq_true_eq]

theorem guard_false (value : A.substitution.Carrier [] sort) (world : Base A) :
    (guard predicate |>.app world value).down = false ↔ ¬ predicate.holds value := by
  change decide (predicate.holds value) = false ↔ _
  simp only [decide_eq_false_iff_not]

theorem positive_classifier
    (defaults : (s : S.Srt) → A.substitution.Carrier [] s) :
    predicate.subfunctor.preimage groundingMap = trueValues.preimage (guard predicate) := by
  rw [positive_grounding_comparison defaults]
  ext world value
  exact (guard_true predicate value world).symm

theorem negative_classifier
    (defaults : (s : S.Srt) → A.substitution.Carrier [] s) :
    (predicate.subfunctor ⇨ ⊥).preimage groundingMap = falseValues.preimage (guard predicate) := by
  rw [negative_grounding_comparison defaults]
  ext world value
  exact (guard_false predicate value world).symm

theorem complementary_at_every_world (world : Base A)
    (value : A.substitution.Carrier [] sort) :
    (value ∈ (trueValues.preimage (guard predicate)).obj world ∨
      value ∈ (falseValues.preimage (guard predicate)).obj world) ∧
    ¬ (value ∈ (trueValues.preimage (guard predicate)).obj world ∧
      value ∈ (falseValues.preimage (guard predicate)).obj world) := by
  constructor
  · cases reading : (guard predicate |>.app world value).down with
    | false => exact Or.inr reading
    | true => exact Or.inl reading
  · rintro ⟨positive, negative⟩
    have impossible : true = false := positive.symm.trans negative
    cases impossible

end Mettapedia.OSLF.Binding.BindingClosedPredicateGuard
