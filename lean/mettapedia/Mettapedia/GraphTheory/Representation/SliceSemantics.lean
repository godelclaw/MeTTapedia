import Mettapedia.GraphTheory.Representation.Basic
import Mettapedia.CategoryTheory.SliceObservation

/-!
# Graph representations in Mathlib's category of meanings

The graph-specific representation portfolio carries algorithms and resource
observers. Forgetting those fields gives an object of `Over` the graph domain.
Its existing refinements are exactly the morphisms in this slice, not merely
a subclass of semantically valid functions. This fully faithful comparison
lets the general observation-change results apply without replacing graph
algorithms by a new abstract machine.
-/

set_option autoImplicit false

open CategoryTheory

namespace Mettapedia.GraphTheory.Representation.SliceSemantics

universe u

variable {n : Nat}

/-- Keep a presentation's carrier and graph denotation. The universe lift
allows the carrier universe to remain arbitrary. -/
def object (presentation : Presentation.{u} n) :
    Over (ULift.{u} (SimpleGraph (Fin n))) :=
  Over.mk (TypeCat.ofHom fun graph => ULift.up (presentation.denote graph))

/-- Existing graph refinements are precisely the concrete commuting
triangles in Mathlib's slice category. -/
def refinementEquiv (source target : Presentation.{u} n) :
    Refinement source target ≃ (object source ⟶ object target) where
  toFun refinement := Over.homMk (TypeCat.ofHom refinement.map) (by
    apply ConcreteCategory.ext_apply
    intro graph
    exact congrArg ULift.up (refinement.commute graph))
  invFun arrow :=
    { map := arrow.left
      commute := fun graph =>
        congrArg ULift.down (ConcreteCategory.congr_hom (Over.w arrow) graph) }
  left_inv refinement := by
    apply Refinement.ext
    rfl
  right_inv arrow := by
    apply Over.OverMorphism.ext
    rfl

@[simp] theorem refinementEquiv_left (source target : Presentation.{u} n)
    (refinement : Refinement source target) :
    ((refinementEquiv source target) refinement).left = TypeCat.ofHom refinement.map :=
  rfl

/-- The category already used by graph conversion is a fully faithful
concrete category over the independent graph meaning. -/
def semantics (n : Nat) :
    Presentation.{u} n ⥤ Over (ULift.{u} (SimpleGraph (Fin n))) where
  obj := object
  map := (refinementEquiv _ _)
  map_id presentation := by
    apply Over.OverMorphism.ext
    rfl
  map_comp earlier later := by
    apply Over.OverMorphism.ext
    rfl

instance semantics_faithful (n : Nat) : (semantics.{u} n).Faithful where
  map_injective := by
    intro source target first second same
    exact (refinementEquiv source target).injective same

instance semantics_full (n : Nat) : (semantics.{u} n).Full where
  map_surjective := by
    intro source target arrow
    exact (refinementEquiv source target).surjective arrow

/-- Every property of the independent graph meaning transports across an
existing refinement, irrespective of the chosen storage and query algorithm. -/
theorem refinement_property_iff {source target : Presentation.{u} n}
    (refinement : Refinement source target)
    (property : SimpleGraph (Fin n) → Prop) (graph : source.Carrier) :
    property (target.denote (refinement.map graph)) ↔ property (source.denote graph) := by
  rw [refinement.commute]

/-- Refinements preserve all selected observations of the graph meaning. -/
theorem refinement_observation_eq {source target : Presentation.{u} n}
    (refinement : Refinement source target) {Observation : Type*}
    (observe : SimpleGraph (Fin n) → Observation) (graph : source.Carrier) :
    observe (target.denote (refinement.map graph)) = observe (source.denote graph) :=
  congrArg observe (refinement.commute graph)

end Mettapedia.GraphTheory.Representation.SliceSemantics
