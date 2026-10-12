import Mettapedia.TypeTheory.CwfYonedaArgumentLift
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

/-!
# The generic future argument of an original dependent type

The actual substituted source comprehension is initial among all future
environments equipped with an argument. Its universal map is the unique
cartesian argument lift. Both the future route and the original argument
are retained; no restriction on which future maps may be tested is imposed.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.CwfYoneda

open CategoryTheory Opposite
open Mettapedia.GSLT.Core.ContextualLadder

universe u w w'
variable (C : Cwf.{u, u, w, w'})

local instance originalContextElements (Γ : C.Ctx) :
    Category.{u} (contextFace C Γ).Elements :=
  CategoryTheory.categoryOfElements (contextFace C Γ)

local instance originalArgumentElements {Γ : C.Ctx} (A : C.Ty Γ) :
    Category.{u} (family C A).Elements :=
  CategoryTheory.categoryOfElements (family C A)

abbrev FutureArguments {Γ Δ : C.Ctx} (A : C.Ty Γ) (σ : C.Sub Δ Γ) :=
  @StructuredArrow (family C A).Elements
    (CategoryTheory.categoryOfElements (family C A))
    (contextFace C Γ).Elements (CategoryTheory.categoryOfElements (contextFace C Γ))
    ⟨op (context C Δ), σ⟩ (CategoryOfElements.π (family C A))

instance futureArgumentsCategory {Γ Δ : C.Ctx} (A : C.Ty Γ) (σ : C.Sub Δ Γ) :
    Category.{u} (FutureArguments C A σ) :=
  @CategoryTheory.instCategoryStructuredArrow (family C A).Elements
    (CategoryTheory.categoryOfElements (family C A))
    (contextFace C Γ).Elements (CategoryTheory.categoryOfElements (contextFace C Γ))
    ⟨op (context C Δ), σ⟩ (CategoryOfElements.π (family C A))

def genericArgument {Γ Δ : C.Ctx} (A : C.Ty Γ) (σ : C.Sub Δ Γ) :
    FutureArguments C A σ :=
  ⟨⟨⟨⟩⟩,
    ⟨⟨op (context C (C.ext Δ (C.tySub A σ))),
          C.compS σ (C.wk (C.tySub A σ))⟩,
        ⟨TypeOver.extensionSubstitution σ A,
          TypeOver.wk_extensionSubstitution σ A⟩⟩,
    (CategoryOfElements.homMk (F := contextFace C Γ) _
      _
      (show op (context C Δ) ⟶ op (context C (C.ext Δ (C.tySub A σ))) from
        (show context C (C.ext Δ (C.tySub A σ)) ⟶ context C Δ from
          C.wk (C.tySub A σ)).op) rfl)⟩

def futureArgumentLift {Γ Δ : C.Ctx} (A : C.Ty Γ) (σ : C.Sub Δ Γ)
    (future : FutureArguments C A σ) :
    C.Sub future.right.1.1.unop.val (C.ext Δ (C.tySub A σ)) :=
  (liftArgument C A σ future.hom.val.unop
    ⟨future.right.2.val, future.right.2.property.trans future.hom.property.symm⟩).val

theorem futureArgumentLift_projection {Γ Δ : C.Ctx}
    (A : C.Ty Γ) (σ : C.Sub Δ Γ) (future : FutureArguments C A σ) :
    C.compS (C.wk (C.tySub A σ)) (futureArgumentLift C A σ future) =
      future.hom.val.unop :=
  liftArgument_projection C A σ _ _

theorem futureArgumentLift_original {Γ Δ : C.Ctx}
    (A : C.Ty Γ) (σ : C.Sub Δ Γ) (future : FutureArguments C A σ) :
    C.compS (TypeOver.extensionSubstitution σ A) (futureArgumentLift C A σ future) =
      future.right.2.val :=
  liftArgument_original C A σ _ _

def genericArgumentMap {Γ Δ : C.Ctx} (A : C.Ty Γ) (σ : C.Sub Δ Γ)
    (future : FutureArguments C A σ) : genericArgument C A σ ⟶ future :=
  StructuredArrow.homMk
    (CategoryOfElements.homMk (F := family C A) _ _
      (CategoryOfElements.homMk (F := contextFace C Γ) _ _
        (show op (context C (C.ext Δ (C.tySub A σ))) ⟶ future.right.1.1 from
          (show context C future.right.1.1.unop.val ⟶
            context C (C.ext Δ (C.tySub A σ)) from futureArgumentLift C A σ future).op)
        (by
          change C.compS (C.compS σ (C.wk (C.tySub A σ)))
            (futureArgumentLift C A σ future) = future.right.1.2
          rw [C.comp_assoc, futureArgumentLift_projection]
          exact future.hom.property))
      (by
        apply Subtype.ext
        exact futureArgumentLift_original C A σ future))
    (by
      apply CategoryOfElements.ext (contextFace C Γ)
      apply Quiver.Hom.unop_inj
      exact futureArgumentLift_projection C A σ future)

theorem genericArgumentMap_unique {Γ Δ : C.Ctx}
    (A : C.Ty Γ) (σ : C.Sub Δ Γ) (future : FutureArguments C A σ)
    (candidate : genericArgument C A σ ⟶ future) :
    candidate = genericArgumentMap C A σ future := by
  apply StructuredArrow.hom_ext
  apply CategoryOfElements.ext (family C A)
  apply CategoryOfElements.ext (contextFace C Γ)
  apply Quiver.Hom.unop_inj
  apply liftArgument_unique C A σ future.hom.val.unop
    ⟨future.right.2.val, future.right.2.property.trans future.hom.property.symm⟩
  · have triangle := congrArg (fun arrow => arrow.val.unop) (StructuredArrow.w candidate)
    exact triangle
  · have original := congrArg Subtype.val candidate.right.property
    exact original

/-- Complete future arguments have the actual source generic argument as
an initial object, with its earned unique cartesian map. -/
def genericArgumentInitial {Γ Δ : C.Ctx} (A : C.Ty Γ) (σ : C.Sub Δ Γ) :
    Limits.IsInitial (genericArgument C A σ) :=
  Limits.IsInitial.ofUniqueHom (genericArgumentMap C A σ)
    (genericArgumentMap_unique C A σ)

end Mettapedia.TypeTheory.CwfYoneda
