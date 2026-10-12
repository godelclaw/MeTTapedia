import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubePresheafCode

/-!
# Universal property of the actual free cube code presheaf

Every natural interpretation of operational generators, sort constants and
authored former operations extends uniquely to the generated code presheaf.
The source carrier injection is retained pointwise and is injective.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubePresheafUniversalProperty

open _root_.CategoryTheory Opposite
open CubeEnrichment

universe u
variable {D : CubeEnrichment.Signature} {W : Type u} [Category.{u} W]
variable (operational target : D.Carrier → Wᵒᵖ ⥤ Type u)

/-- A target algebra interprets the declared generators naturally. These
operation laws specify target structures, not an assumed extension map. -/
structure Algebra where
  atWorld : ∀ world, CubeEnrichment.Code.Algebra (signature := D)
    (operational := fun carrier => (operational carrier).obj world)
    (fun carrier => (target carrier).obj world)
  operational_natural : ∀ {first second} (arrow : first ⟶ second) {carrier} value,
    (atWorld second).operational ((operational carrier).map arrow value) =
      (target carrier).map arrow ((atWorld first).operational value)
  sort_natural : ∀ {first second} (arrow : first ⟶ second) {carrier} sort,
    (atWorld second).sort (carrier := carrier) sort =
      (target carrier).map arrow ((atWorld first).sort sort)
  former_natural : ∀ {first second} (arrow : first ⟶ second) declaration
    (arguments : ∀ position, (target (D.input declaration position)).obj first),
    (atWorld second).former declaration (fun position =>
      (target (D.input declaration position)).map arrow (arguments position)) =
      (target (D.output declaration)).map arrow ((atWorld first).former declaration arguments)

variable {operational target}

theorem fold_natural (algebra : Algebra operational target)
    {first second : Wᵒᵖ} (arrow : first ⟶ second) {carrier : D.Carrier}
    (code : (CubePresheafCode.presheaf operational carrier).obj first) :
    CubeEnrichment.Code.fold (algebra.atWorld second)
      ((CubePresheafCode.presheaf operational carrier).map arrow code) =
      (target carrier).map arrow (CubeEnrichment.Code.fold (algebra.atWorld first) code) := by
  induction code with
  | operational value => exact algebra.operational_natural arrow value
  | sort sort => exact algebra.sort_natural arrow sort
  | former declaration arguments hypotheses =>
      change (algebra.atWorld second).former declaration (fun position =>
        CubeEnrichment.Code.fold (algebra.atWorld second)
          (CubePresheafCode.Code.map (fun carrier => (operational carrier).map arrow) (arguments position))) = _
      have components : (fun position => CubeEnrichment.Code.fold (algebra.atWorld second)
          (CubePresheafCode.Code.map (fun carrier => (operational carrier).map arrow) (arguments position))) =
          fun position => (target (D.input declaration position)).map arrow
            (CubeEnrichment.Code.fold (algebra.atWorld first) (arguments position)) := by
        funext position
        exact hypotheses position
      rw [components]
      exact algebra.former_natural arrow declaration _

def extend (algebra : Algebra operational target) (carrier : D.Carrier) :
    CubePresheafCode.presheaf operational carrier ⟶ target carrier where
  app world := TypeCat.ofHom (CubeEnrichment.Code.fold (algebra.atWorld world))
  naturality first second arrow := by
    apply ConcreteCategory.hom_ext
    intro code
    exact fold_natural algebra arrow code

theorem extends_operational (algebra : Algebra operational target) (carrier : D.Carrier)
    (world : Wᵒᵖ) (value : (operational carrier).obj world) :
    (extend algebra carrier).app world ((CubePresheafCode.injection operational carrier).app world value) =
      (algebra.atWorld world).operational value := rfl

theorem extends_sort (algebra : Algebra operational target) (carrier : D.Carrier)
    (world : Wᵒᵖ) (sort : Mettapedia.OSLF.Framework.ModalHypercube.HSort) :
    (extend algebra carrier).app world (.sort sort) = (algebra.atWorld world).sort sort := rfl

theorem extends_former (algebra : Algebra operational target) (declaration : D.Former)
    (world : Wᵒᵖ) (arguments : ∀ position,
      (CubePresheafCode.presheaf operational (D.input declaration position)).obj world) :
    (extend algebra (D.output declaration)).app world (.former declaration arguments) =
      (algebra.atWorld world).former declaration
        (fun position => (extend algebra (D.input declaration position)).app world (arguments position)) := rfl

/-- Uniqueness is proved for every code by induction on the independent free
syntax; no extension or whole-language equality is supplied as a hypothesis. -/
theorem extension_unique (algebra : Algebra operational target)
    (candidate : ∀ carrier, CubePresheafCode.presheaf operational carrier ⟶ target carrier)
    (onOperational : ∀ carrier world value,
      (candidate carrier).app world (.operational value) = (algebra.atWorld world).operational value)
    (onSort : ∀ carrier world sort,
      (candidate carrier).app world (.sort sort) = (algebra.atWorld world).sort sort)
    (onFormer : ∀ declaration world arguments,
      (candidate (D.output declaration)).app world (.former declaration arguments) =
      (algebra.atWorld world).former declaration
        (fun position => (candidate (D.input declaration position)).app world (arguments position))) :
    candidate = extend algebra := by
  funext carrier
  apply NatTrans.ext
  funext world
  apply ConcreteCategory.hom_ext
  intro code
  exact CubeEnrichment.Code.fold_unique (algebra.atWorld world)
    (fun {carrier} => (candidate carrier).app world)
    (onOperational · world) (onSort · world) (onFormer · world) carrier code

end Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubePresheafUniversalProperty
