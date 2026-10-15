import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeEnrichment
import Mettapedia.TypeTheory.DisplayedPresheafTransport

/-!
# Free cube enrichment as an actual presheaf

Restriction maps the operational generators and retains every sort constant,
former index and ordered argument code. The kinding projection uses the
independently defined formation judgment; it is not a supplied predicate.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubePresheafCode

open CategoryTheory Opposite
open CubeEnrichment
open Mettapedia.OSLF.Framework.ModalHypercube (HSort)
open Mettapedia.TypeTheory.DisplayedPresheafTransport

universe u v w
variable {D : CubeEnrichment.Signature}

namespace Code

variable {A : D.Carrier → Type u} {B : D.Carrier → Type u} {E : D.Carrier → Type u}

def map (f : ∀ carrier, A carrier → B carrier) :
    {carrier : D.Carrier} → CubeEnrichment.Code D A carrier → CubeEnrichment.Code D B carrier :=
  CubeEnrichment.Code.fold (signature := D) (operational := A)
    (target := fun carrier => CubeEnrichment.Code D B carrier) ⟨(fun {carrier} value => .operational (f carrier value)),
    (fun sort => .sort sort), (fun declaration arguments => .former declaration arguments)⟩

@[simp] theorem map_operational (f : ∀ carrier, A carrier → B carrier)
    {carrier : D.Carrier} (value : A carrier) : map f (.operational value) = .operational (f carrier value) := rfl

@[simp] theorem map_sort (f : ∀ carrier, A carrier → B carrier) {carrier : D.Carrier} (sort : HSort) :
    map f (.sort sort : CubeEnrichment.Code D A carrier) = .sort sort := rfl

@[simp] theorem map_former (f : ∀ carrier, A carrier → B carrier) (declaration : D.Former)
    (arguments : ∀ position, CubeEnrichment.Code D A (D.input declaration position)) :
    map f (.former declaration arguments) = .former declaration (fun position => map f (arguments position)) := rfl

theorem map_id {carrier : D.Carrier} (code : CubeEnrichment.Code D A carrier) :
    map (fun _ value => value) code = code := by
  induction code with
  | operational => rfl
  | sort => rfl
  | former declaration arguments hypotheses =>
      simp only [map_former]
      congr 1
      funext position
      exact hypotheses position

theorem map_comp (f : ∀ carrier, A carrier → B carrier) (g : ∀ carrier, B carrier → E carrier)
    {carrier : D.Carrier} (code : CubeEnrichment.Code D A carrier) :
    map g (map f code) = map (fun carrier value => g carrier (f carrier value)) code := by
  induction code with
  | operational => rfl
  | sort => rfl
  | former declaration arguments hypotheses =>
      simp only [map_former]
      congr 1
      funext position
      exact hypotheses position

end Code

namespace Kinded

variable {A : D.Carrier → Type u} {B : D.Carrier → Type u} {vertex : Vertex D}

def map (f : ∀ carrier, A carrier → B carrier) {carrier : D.Carrier}
    {code : CubeEnrichment.Code D A carrier} {kind : HSort} :
    CubeEnrichment.Kinded vertex code kind → CubeEnrichment.Kinded vertex (Code.map f code) kind
  | .star => .star
  | .former declaration arguments premises =>
      .former declaration (fun position => Code.map f (arguments position))
        (fun position => map f (premises position))

end Kinded

variable {W : Type u} [Category.{u} W]
variable (operational : D.Carrier → Wᵒᵖ ⥤ Type u)

/-- The free carrier is constructed worldwise from the actual old carriers. -/
def presheaf (carrier : D.Carrier) : Wᵒᵖ ⥤ Type u where
  obj world := CubeEnrichment.Code D (fun carrier => (operational carrier).obj world) carrier
  map arrow := TypeCat.ofHom (Code.map (fun carrier => (operational carrier).map arrow))
  map_id world := by
    ext code
    have identity : (fun carrier => ((operational carrier).map (𝟙 world) : _ → _)) = fun _ value => value := by
      funext carrier
      funext value
      exact ConcreteCategory.congr_hom ((operational carrier).map_id world) value
    change Code.map (fun carrier => (operational carrier).map (𝟙 world)) code = code
    rw [identity, Code.map_id]
  map_comp first second := by
    ext code
    change Code.map (fun carrier => (operational carrier).map (first ≫ second)) code =
      Code.map (fun carrier => (operational carrier).map second)
        (Code.map (fun carrier => (operational carrier).map first) code)
    rw [Code.map_comp]
    congr 1
    funext carrier value
    exact ConcreteCategory.congr_hom ((operational carrier).map_comp first second) value

def injection (carrier : D.Carrier) : operational carrier ⟶ presheaf operational carrier where
  app world := TypeCat.ofHom (@CubeEnrichment.Code.operational D
    (fun carrier => (operational carrier).obj world) carrier)
  naturality _ _ _ := by
    apply ConcreteCategory.hom_ext
    intro value
    rfl

theorem injection_monic (carrier : D.Carrier) (world : Wᵒᵖ) :
    Function.Injective ((injection operational carrier).app world) :=
  fun _ _ equal => CubeEnrichment.Code.operational_injective equal

def sort (carrier : D.Carrier) (kind : HSort) :
    (Functor.const Wᵒᵖ).obj PUnit ⟶ presheaf operational carrier where
  app _ := TypeCat.ofHom (fun _ => .sort kind)
  naturality _ _ _ := rfl

/-- Complete typed codes form a presheaf, with the selected kind retained. -/
def typedPresheaf (vertex : Vertex D) (carrier : D.Carrier) : Wᵒᵖ ⥤ Type u where
  obj world := Σ kind : HSort,
    {code : (presheaf operational carrier).obj world // Nonempty (CubeEnrichment.Kinded vertex code kind)}
  map arrow := TypeCat.ofHom fun value =>
    ⟨value.1, (presheaf operational carrier).map arrow value.2.1,
      value.2.2.map (Kinded.map (fun carrier => (operational carrier).map arrow))⟩
  map_id world := by
    apply ConcreteCategory.hom_ext
    intro value
    change (⟨value.1, ⟨(presheaf operational carrier).map (𝟙 world) value.2.1, _⟩⟩ :
      Σ kind : HSort, {code : (presheaf operational carrier).obj world //
        Nonempty (CubeEnrichment.Kinded vertex code kind)}) = value
    refine @Sigma.ext HSort (fun kind => {code : (presheaf operational carrier).obj world //
      Nonempty (CubeEnrichment.Kinded vertex code kind)}) _ _ rfl ?_
    apply heq_of_eq
    apply Subtype.ext
    exact ConcreteCategory.congr_hom ((presheaf operational carrier).map_id world) value.2.1
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro value
    change (⟨value.1, ⟨(presheaf operational carrier).map (first ≫ second) value.2.1, _⟩⟩ :
      Σ kind : HSort, {code : (presheaf operational carrier).obj _ //
        Nonempty (CubeEnrichment.Kinded vertex code kind)}) =
      ⟨value.1, ⟨(presheaf operational carrier).map second
        ((presheaf operational carrier).map first value.2.1), _⟩⟩
    refine @Sigma.ext HSort (fun kind => {code : (presheaf operational carrier).obj _ //
      Nonempty (CubeEnrichment.Kinded vertex code kind)}) _ _ rfl ?_
    apply heq_of_eq
    apply Subtype.ext
    exact ConcreteCategory.congr_hom ((presheaf operational carrier).map_comp first second) value.2.1

/-- The ordered pair is (code, its selected sort constant). -/
def pairPresheaf (carrier : D.Carrier) : Wᵒᵖ ⥤ Type u where
  obj world := (presheaf operational carrier).obj world × (presheaf operational carrier).obj world
  map arrow := TypeCat.ofHom fun pair =>
    ((presheaf operational carrier).map arrow pair.1,
     (presheaf operational carrier).map arrow pair.2)
  map_id world := by ext pair <;> simp
  map_comp first second := by ext pair <;> simp

def typingProjection (vertex : Vertex D) (carrier : D.Carrier) :
    typedPresheaf operational vertex carrier ⟶ pairPresheaf operational carrier where
  app _ := TypeCat.ofHom fun value => (value.2.1, .sort value.1)
  naturality _ _ _ := rfl

abbrev typingFamily (vertex : Vertex D) (carrier : D.Carrier) :=
  observationFibreFamily (typingProjection operational vertex carrier)

/-- Inhabitation of the independently constructed fibre is exactly the
independent kind-formation judgment at the displayed code and sort. -/
theorem fibre_inhabited_iff (vertex : Vertex D) (carrier : D.Carrier) (world : Wᵒᵖ)
    (code : (presheaf operational carrier).obj world) (kind : HSort) :
    Nonempty ((typingFamily operational vertex carrier).obj ⟨world, (code, .sort kind)⟩) ↔
      Nonempty (CubeEnrichment.Kinded vertex code kind) := by
  constructor
  · rintro ⟨value⟩
    have codeEqual : value.val.2.1 = code := congrArg Prod.fst value.property
    have kindEqual : value.val.1 = kind := CubeEnrichment.Code.sort.inj (congrArg Prod.snd value.property)
    exact (congrArg₂ (fun c k => Nonempty (CubeEnrichment.Kinded vertex c k)) codeEqual kindEqual) ▸ value.val.2.2
  · intro formed
    exact ⟨⟨⟨kind, ⟨code, formed⟩⟩, rfl⟩⟩

/-- The code and selected sort are retained by every actual fibre value. -/
theorem fibre_origin (vertex : Vertex D) (carrier : D.Carrier) (world : Wᵒᵖ)
    (code : (presheaf operational carrier).obj world) (kind : HSort)
    (value : (typingFamily operational vertex carrier).obj ⟨world, (code, .sort kind)⟩) :
    value.val.2.1 = code ∧ value.val.1 = kind :=
  ⟨congrArg Prod.fst value.property,
    CubeEnrichment.Code.sort.inj (congrArg Prod.snd value.property)⟩

end Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubePresheafCode
