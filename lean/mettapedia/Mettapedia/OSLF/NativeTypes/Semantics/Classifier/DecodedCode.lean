import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeEnrichment
import Mettapedia.TypeTheory.DisplayedPresheafTransport
import Mettapedia.GSLT.Topos.NativePowerPredicates

/-!
# Classifiers over the original operational presheaves

A classifier retains its actual local power section, including every future
world and argument. Operational values and the two sort tags remain distinct.
This is a predicate interpretation, rather than the free code interpretation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Classifier

open _root_.CategoryTheory Opposite
open Presheaf.CubeEnrichment
open Mettapedia.OSLF.Framework.ModalHypercube (HSort)
open Mettapedia.TypeTheory.DisplayedPresheafTransport
open Mettapedia.GSLT.Topos

universe u
variable {D : Presheaf.CubeEnrichment.Signature} {W : Type u} [Category.{u} W]

inductive Code (operational : D.Carrier → Wᵒᵖ ⥤ Type u) (carrier : D.Carrier)
    (world : Wᵒᵖ) : Type u where
  | operational (value : (operational carrier).obj world)
  | sort (kind : HSort)
  | classifier (kind : HSort) (predicate : (NativePowerPredicates.power (operational carrier)).obj world)

namespace Code
variable {operational : D.Carrier → Wᵒᵖ ⥤ Type u} {carrier : D.Carrier}

def map {world future : Wᵒᵖ} (arrow : world ⟶ future) :
    Code operational carrier world → Code operational carrier future
  | .operational value => .operational ((operational carrier).map arrow value)
  | .sort kind => .sort kind
  | .classifier kind predicate => .classifier kind
      ((NativePowerPredicates.power (operational carrier)).map arrow predicate)

theorem map_id {world : Wᵒᵖ} (code : Code operational carrier world) : map (𝟙 world) code = code := by
  cases code with
  | operational value =>
      exact congrArg Code.operational
        (ConcreteCategory.congr_hom ((operational carrier).map_id world) value)
  | sort => rfl
  | classifier kind predicate =>
      exact congrArg (Code.classifier kind)
        (ConcreteCategory.congr_hom ((NativePowerPredicates.power (operational carrier)).map_id world) predicate)

theorem map_comp {world middle future : Wᵒᵖ} (first : world ⟶ middle) (second : middle ⟶ future)
    (code : Code operational carrier world) : map (first ≫ second) code = map second (map first code) := by
  cases code with
  | operational value =>
      exact congrArg Code.operational
        (ConcreteCategory.congr_hom ((operational carrier).map_comp first second) value)
  | sort => rfl
  | classifier kind predicate =>
      exact congrArg (Code.classifier kind)
        (ConcreteCategory.congr_hom ((NativePowerPredicates.power (operational carrier)).map_comp first second) predicate)

noncomputable def Member {world : Wᵒᵖ} : Code operational carrier world → Code operational carrier world → Prop
  | .operational value, .classifier _ predicate =>
      (value, predicate) ∈ (NativePowerPredicates.membership (operational carrier)).obj world
  | .classifier kind _, .sort claimed => kind = claimed
  | .sort .star, .sort .box => True
  | _, _ => False

theorem member_map {world future : Wᵒᵖ} (arrow : world ⟶ future)
    {value type : Code operational carrier world} (member : Member value type) :
    Member (map arrow value) (map arrow type) := by
  cases value <;> cases type <;> simp only [Member] at member ⊢
  case operational.classifier value kind predicate =>
    exact (NativePowerPredicates.membership (operational carrier)).map arrow member
  case sort.sort valueKind typeKind =>
    cases valueKind <;> cases typeKind <;> exact member
  all_goals exact member

@[simp] theorem operational_member {world : Wᵒᵖ}
    (value : (operational carrier).obj world) (kind : HSort)
    (predicate : (NativePowerPredicates.power (operational carrier)).obj world) :
    Member (.operational value) (.classifier kind predicate) ↔
      (value, predicate) ∈ (NativePowerPredicates.membership (operational carrier)).obj world := Iff.rfl

@[simp] theorem classifier_kinded {world : Wᵒᵖ} (kind claimed : HSort)
    (predicate : (NativePowerPredicates.power (operational carrier)).obj world) :
    Member (.classifier kind predicate) (.sort claimed) ↔ kind = claimed := Iff.rfl

theorem star_box (carrier : D.Carrier) (world : Wᵒᵖ) :
    Member (.sort .star : Code operational carrier world) (.sort .box) := True.intro

end Code

namespace Carrier
variable (operational : D.Carrier → Wᵒᵖ ⥤ Type u)

def presheaf (carrier : D.Carrier) : Wᵒᵖ ⥤ Type u where
  obj world := Code operational carrier world
  map arrow := TypeCat.ofHom (Code.map arrow)
  map_id _ := by ext value; exact Code.map_id value
  map_comp first second := by ext value; exact Code.map_comp first second value

def injection (carrier : D.Carrier) : operational carrier ⟶ presheaf operational carrier where
  app _ := TypeCat.ofHom Code.operational
  naturality _ _ _ := rfl

def classifierName {P : Wᵒᵖ ⥤ Type u} (carrier : D.Carrier) (kind : HSort)
    (predicate : P ⟶ NativePowerPredicates.power (operational carrier)) :
    P ⟶ presheaf operational carrier where
  app world := TypeCat.ofHom fun value => .classifier kind (predicate.app world value)
  naturality world future arrow := by
    ext value
    exact congrArg (Code.classifier kind) (predicate.naturality_apply arrow value)

def pairPresheaf (carrier : D.Carrier) : Wᵒᵖ ⥤ Type u :=
  FunctorToTypes.prod (presheaf operational carrier) (presheaf operational carrier)

noncomputable def membership (carrier : D.Carrier) : Subfunctor (pairPresheaf operational carrier) where
  obj _ := fun pair => Code.Member pair.1 pair.2
  map arrow _ member := Code.member_map arrow member

noncomputable def typedPresheaf (carrier : D.Carrier) : Wᵒᵖ ⥤ Type u :=
  (membership operational carrier).toFunctor

noncomputable def typingProjection (carrier : D.Carrier) :
    typedPresheaf operational carrier ⟶ pairPresheaf operational carrier :=
  (membership operational carrier).ι

noncomputable abbrev typingFamily (carrier : D.Carrier) :=
  observationFibreFamily (typingProjection operational carrier)

theorem fibre_inhabited_iff (carrier : D.Carrier) (world : Wᵒᵖ)
    (value type : Code operational carrier world) :
    Nonempty ((typingFamily operational carrier).obj ⟨world, (value, type)⟩) ↔ Code.Member value type := by
  constructor
  · rintro ⟨witness⟩
    have same : witness.val.val = (value, type) := witness.property
    exact (congrArg (fun pair => Code.Member pair.1 pair.2) same) ▸ witness.val.property
  · intro member
    exact ⟨⟨⟨(value, type), member⟩, rfl⟩⟩

end Carrier
end Mettapedia.OSLF.NativeTypes.Semantics.Classifier
