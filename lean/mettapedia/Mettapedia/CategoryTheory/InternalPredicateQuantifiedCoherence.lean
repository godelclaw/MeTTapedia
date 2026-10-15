import Mettapedia.CategoryTheory.InternalPredicateQuantifiedObject
import Mettapedia.CategoryTheory.PositionedModalOutgoingComparison

/-!
# Complete identity, composition and isomorphism laws for internal quantifiers

The local quantifier diagrams earn adjunctions at every generalized
context. Uniqueness of those adjoints gives identity and composition on
the complete function-object arrows. At an actual carrier isomorphism,
both quantifiers are inverse precomposition. These are earned coherence
laws, independent of any chosen presentation of a native predicate model.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.InternalPredicateQuantifiedCoherence

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open InternalPredicateFunctionObject InternalPredicateQuantifier
open PositionedModalOutgoingComparison

universe u v
variable {C : Type u} [Category.{v} C]
variable [CartesianMonoidalCategory C] [MonoidalClosed C] [HasEqualizers C]
variable (operations : InternalPredicateQuantifiedObject.Operations C)

theorem universal_identity (value : C) :
    (operations.universal (𝟙 value)).operation = 𝟙 (power operations.predicates value) := by
  let context := power operations.predicates value
  let : SemilatticeInf (context ⟶ power operations.predicates value) :=
    (functions operations.predicates value).semilattice
      (functionLaws operations.predicates operations.laws value) context
  have complete : 𝟙 context ≫ (operations.universal (𝟙 value)).operation = 𝟙 context :=
    (operations.universal_galois (𝟙 value) context).u_unique GaloisConnection.id
      (fun predicate => by rw [precomposition_identity, Category.comp_id]; rfl)
  simpa only [Category.id_comp] using complete

theorem existential_identity (value : C) :
    (operations.existential (𝟙 value)).operation = 𝟙 (power operations.predicates value) := by
  let context := power operations.predicates value
  let : SemilatticeInf (context ⟶ power operations.predicates value) :=
    (functions operations.predicates value).semilattice
      (functionLaws operations.predicates operations.laws value) context
  have complete : 𝟙 context ≫ (operations.existential (𝟙 value)).operation = 𝟙 context :=
    (operations.existential_galois (𝟙 value) context).l_unique GaloisConnection.id
      (fun predicate => by rw [precomposition_identity, Category.comp_id]; rfl)
  simpa only [Category.id_comp] using complete

theorem existential_composition {first second third : C}
    (before : first ⟶ second) (after : second ⟶ third) :
    (operations.existential (before ≫ after)).operation =
      (operations.existential before).operation ≫ (operations.existential after).operation := by
  let context := power operations.predicates first
  let : SemilatticeInf (context ⟶ power operations.predicates first) :=
    (functions operations.predicates first).semilattice
      (functionLaws operations.predicates operations.laws first) context
  let : SemilatticeInf (context ⟶ power operations.predicates second) :=
    (functions operations.predicates second).semilattice
      (functionLaws operations.predicates operations.laws second) context
  let : SemilatticeInf (context ⟶ power operations.predicates third) :=
    (functions operations.predicates third).semilattice
      (functionLaws operations.predicates operations.laws third) context
  have composed := (operations.existential_galois before context).compose
    (operations.existential_galois after context)
  have complete : 𝟙 context ≫ (operations.existential (before ≫ after)).operation =
      (𝟙 context ≫ (operations.existential before).operation) ≫ (operations.existential after).operation :=
    (operations.existential_galois (before ≫ after) context).l_unique composed
      (fun predicate => by simp only [Function.comp_apply, precomposition_composition, Category.assoc])
  simpa only [Category.id_comp] using complete

theorem universal_composition {first second third : C}
    (before : first ⟶ second) (after : second ⟶ third) :
    (operations.universal (before ≫ after)).operation =
      (operations.universal before).operation ≫ (operations.universal after).operation := by
  let context := power operations.predicates first
  let : SemilatticeInf (context ⟶ power operations.predicates first) :=
    (functions operations.predicates first).semilattice
      (functionLaws operations.predicates operations.laws first) context
  let : SemilatticeInf (context ⟶ power operations.predicates second) :=
    (functions operations.predicates second).semilattice
      (functionLaws operations.predicates operations.laws second) context
  let : SemilatticeInf (context ⟶ power operations.predicates third) :=
    (functions operations.predicates third).semilattice
      (functionLaws operations.predicates operations.laws third) context
  have composed := (operations.universal_galois after context).compose
    (operations.universal_galois before context)
  have complete : 𝟙 context ≫ (operations.universal (before ≫ after)).operation =
      (𝟙 context ≫ (operations.universal before).operation) ≫ (operations.universal after).operation :=
    (operations.universal_galois (before ≫ after) context).u_unique composed
      (fun predicate => by simp only [Function.comp_apply, precomposition_composition, Category.assoc])
  simpa only [Category.id_comp] using complete

theorem inverse_precomposition_galois {before after : C} (comparison : before ≅ after) (context : C) :
    letI : SemilatticeInf (context ⟶ power operations.predicates before) :=
      (functions operations.predicates before).semilattice
        (functionLaws operations.predicates operations.laws before) context
    letI : SemilatticeInf (context ⟶ power operations.predicates after) :=
      (functions operations.predicates after).semilattice
        (functionLaws operations.predicates operations.laws after) context
    GaloisConnection
      (fun predicate : context ⟶ power operations.predicates before =>
        predicate ≫ precomposition operations.predicates comparison.inv)
      (fun predicate : context ⟶ power operations.predicates after =>
        predicate ≫ precomposition operations.predicates comparison.hom) := by
  let : SemilatticeInf (context ⟶ power operations.predicates before) :=
    (functions operations.predicates before).semilattice
      (functionLaws operations.predicates operations.laws before) context
  let : SemilatticeInf (context ⟶ power operations.predicates after) :=
    (functions operations.predicates after).semilattice
      (functionLaws operations.predicates operations.laws after) context
  intro first second
  constructor
  · intro ordered
    have carried := precomposition_mono operations.predicates operations.laws comparison.hom context ordered
    have recovered : (first ≫ precomposition operations.predicates comparison.inv) ≫
        precomposition operations.predicates comparison.hom = first := by
      rw [Category.assoc, ← precomposition_composition, comparison.hom_inv_id,
        precomposition_identity, Category.comp_id]
    exact recovered ▸ carried
  · intro ordered
    have carried := precomposition_mono operations.predicates operations.laws comparison.inv context ordered
    have recovered : (second ≫ precomposition operations.predicates comparison.hom) ≫
        precomposition operations.predicates comparison.inv = second := by
      rw [Category.assoc, ← precomposition_composition, comparison.inv_hom_id,
        precomposition_identity, Category.comp_id]
    exact recovered ▸ carried

theorem existential_isomorphism {before after : C} (comparison : before ≅ after) :
    (operations.existential comparison.hom).operation =
      (powerReindexIso operations.predicates comparison).hom := by
  change (operations.existential comparison.hom).operation =
    precomposition operations.predicates comparison.inv
  let context := power operations.predicates before
  let : SemilatticeInf (context ⟶ power operations.predicates before) :=
    (functions operations.predicates before).semilattice
      (functionLaws operations.predicates operations.laws before) context
  let : SemilatticeInf (context ⟶ power operations.predicates after) :=
    (functions operations.predicates after).semilattice
      (functionLaws operations.predicates operations.laws after) context
  have complete : 𝟙 context ≫ (operations.existential comparison.hom).operation =
      𝟙 context ≫ precomposition operations.predicates comparison.inv :=
    (operations.existential_galois comparison.hom context).l_unique
      (inverse_precomposition_galois operations comparison context) (fun _ => rfl)
  simpa only [Category.id_comp] using complete

theorem universal_isomorphism {before after : C} (comparison : before ≅ after) :
    (operations.universal comparison.hom).operation =
      (powerReindexIso operations.predicates comparison).hom := by
  change (operations.universal comparison.hom).operation =
    precomposition operations.predicates comparison.inv
  let context := power operations.predicates before
  let : SemilatticeInf (context ⟶ power operations.predicates before) :=
    (functions operations.predicates before).semilattice
      (functionLaws operations.predicates operations.laws before) context
  let : SemilatticeInf (context ⟶ power operations.predicates after) :=
    (functions operations.predicates after).semilattice
      (functionLaws operations.predicates operations.laws after) context
  have complete : 𝟙 context ≫ (operations.universal comparison.hom).operation =
      𝟙 context ≫ precomposition operations.predicates comparison.inv :=
    (operations.universal_galois comparison.hom context).u_unique
      (inverse_precomposition_galois operations comparison.symm context) (fun _ => rfl)
  simpa only [Category.id_comp] using complete

theorem existential_outgoing_comparison {arguments before after : C}
    (constructor : arguments ⟶ before) (comparison : before ≅ after) :
    (operations.existential constructor).operation ≫ (powerReindexIso operations.predicates comparison).hom =
      (operations.existential (constructor ≫ comparison.hom)).operation := by
  rw [existential_composition, existential_isomorphism]

theorem existential_constructor_comparison {arguments actualArguments before after : C}
    (constructor : arguments ⟶ before) (argumentComparison : arguments ≅ actualArguments)
    (programComparison : before ≅ after) :
    (operations.existential constructor).operation ≫
        (powerReindexIso operations.predicates programComparison).hom =
      (powerReindexIso operations.predicates argumentComparison).hom ≫
        (operations.existential
          (argumentComparison.inv ≫ constructor ≫ programComparison.hom)).operation := by
  calc
    _ = (operations.existential (constructor ≫ programComparison.hom)).operation :=
      existential_outgoing_comparison operations constructor programComparison
    _ = (operations.existential
        (argumentComparison.hom ≫ (argumentComparison.inv ≫ constructor ≫ programComparison.hom))).operation := by
      rw [← Category.assoc, argumentComparison.hom_inv_id, Category.id_comp]
    _ = (operations.existential argumentComparison.hom).operation ≫
        (operations.existential (argumentComparison.inv ≫ constructor ≫ programComparison.hom)).operation :=
      existential_composition operations _ _
    _ = _ := congrArg (fun arrow => arrow ≫
      (operations.existential (argumentComparison.inv ≫ constructor ≫ programComparison.hom)).operation)
        (existential_isomorphism operations argumentComparison)

end Mettapedia.CategoryTheory.InternalPredicateQuantifiedCoherence
