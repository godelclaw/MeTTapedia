import Mettapedia.TypeTheory.NativeLocalTypeFormers
import Mettapedia.TypeTheory.DependentProductNativeComparison
import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes

/-!
# Nondependent native functions and genuine presheaf function objects

The domain and codomain displayed families may have arbitrary native local
presentations. Independently supplied natural comparisons to nondependent
presheaf families yield the actual future-argument function object. The
comparison uses the selected native right-Kan product, retaining every
future arrow and argument rather than only current-world functions.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.NativeNondependentFunctionComparison

open _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory
open DisplayedPresheafTransport DisplayedPresheafComprehension
open DisplayedPresheafIndexedCwfBridge DisplayedPresheafPi
open NativeLocalTypeFormers
open Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent

universe u
variable {C : Type u} [Category.{u} C]
variable {P : Cᵒᵖ ⥤ Type u}

def constantFamily (P : Cᵒᵖ ⥤ Type u) (F : Cᵒᵖ ⥤ Type u) : DisplayedFamily P :=
  CategoryOfElements.π P ⋙ F

def future (point : P.Elements) {world : Cᵒᵖ} (arrow : point.1 ⟶ world) : P.Elements :=
  ⟨world, P.map arrow point.2⟩

def futureArrow (point : P.Elements) {world : Cᵒᵖ} (arrow : point.1 ⟶ world) :
    point ⟶ future point arrow := ⟨arrow, rfl⟩

def futureLater (point : P.Elements) {world next : Cᵒᵖ}
    (arrow : point.1 ⟶ world) (later : world ⟶ next) :
    future point arrow ⟶ future point (arrow ≫ later) :=
  ⟨later, (P.map_comp_apply arrow later point.2).symm⟩

def argumentPoint {A : DisplayedFamily P} (point : P.Elements) (argument : A.obj point) :
    (totalSpace A).Elements := ⟨point.1, ⟨point.2, argument⟩⟩

def argumentArrow {A : DisplayedFamily P} {first last : P.Elements}
    (arrow : first ⟶ last) (argument : A.obj first) :
    argumentPoint first argument ⟶ argumentPoint last (A.map arrow argument) :=
  ⟨arrow.val, totalMap_of_base_arrow A arrow argument⟩

theorem displayed_argument_arrow {A : DisplayedFamily P} {first last : P.Elements}
    (arrow : first ⟶ last) (argument : A.obj first) :
    (displayedToTotalElements A).map (argumentMap A arrow argument) =
      argumentArrow arrow argument := by
  apply Subtype.ext
  exact displayedToTotalElements_underlying A (argumentMap A arrow argument)

def sectionToFunction {A : DisplayedFamily P}
    {B : DisplayedFamily (totalSpace A)} {D E : Cᵒᵖ ⥤ Type u}
    (domain : A ≅ constantFamily P D)
    (body : B ≅ constantFamily (totalSpace A) E) (point : P.Elements)
    (witness : DependentSection A (displayedToTotalElements A ⋙ B) point) :
    (D.functorHom E).obj point.1 where
  app world arrow := TypeCat.ofHom fun argument =>
    let target := future point arrow
    let input := domain.inv.app target argument
    body.hom.app (argumentPoint target input)
      (witness.app target (futureArrow point arrow) input)
  naturality := by
    intro world next later arrow
    apply ConcreteCategory.hom_ext
    intro argument
    let target := future point arrow
    let final := future point (arrow ≫ later)
    let change : target ⟶ final := futureLater point arrow later
    let input := domain.inv.app target argument
    have domainLaw := domain.inv.naturality_apply change argument
    change domain.inv.app final (D.map later argument) = A.map change input at domainLaw
    change body.hom.app (argumentPoint final (domain.inv.app final (D.map later argument)))
        (witness.app final (futureArrow point (arrow ≫ later))
          (domain.inv.app final (D.map later argument))) =
      E.map later (body.hom.app (argumentPoint target input)
        (witness.app target (futureArrow point arrow) input))
    rw [domainLaw]
    have bodyLaw := body.hom.naturality_apply (argumentArrow change input)
      (witness.app target (futureArrow point arrow) input)
    change body.hom.app (argumentPoint final (A.map change input))
        (B.map (argumentArrow change input)
          (witness.app target (futureArrow point arrow) input)) = _ at bodyLaw
    have sectionLaw := witness.naturality change (futureArrow point arrow) input
    rw [Functor.comp_map, displayed_argument_arrow] at sectionLaw
    change B.map (argumentArrow change input)
        (witness.app target (futureArrow point arrow) input) =
      witness.app final (futureArrow point (arrow ≫ later)) (A.map change input) at sectionLaw
    rw [sectionLaw] at bodyLaw
    exact bodyLaw

def functionToSection {A : DisplayedFamily P}
    {B : DisplayedFamily (totalSpace A)} {D E : Cᵒᵖ ⥤ Type u}
    (domain : A ≅ constantFamily P D)
    (body : B ≅ constantFamily (totalSpace A) E) (point : P.Elements)
    (function : (D.functorHom E).obj point.1) :
    DependentSection A (displayedToTotalElements A ⋙ B) point where
  app target arrow argument :=
    body.inv.app (argumentPoint target argument)
      (function.app target.1 arrow.val (domain.hom.app target argument))
  naturality := by
    intro first last later arrow argument
    have domainLaw := domain.hom.naturality_apply later argument
    change domain.hom.app last (A.map later argument) =
      D.map later.val (domain.hom.app first argument) at domainLaw
    have functionLaw := ConcreteCategory.congr_hom
      (function.naturality later.val arrow.val) (domain.hom.app first argument)
    change function.app last.1 (arrow.val ≫ later.val)
        (D.map later.val (domain.hom.app first argument)) =
      E.map later.val (function.app first.1 arrow.val
        (domain.hom.app first argument)) at functionLaw
    rw [Functor.comp_map, displayed_argument_arrow]
    change B.map (argumentArrow later argument)
        (body.inv.app (argumentPoint first argument)
          (function.app first.1 arrow.val (domain.hom.app first argument))) =
      body.inv.app (argumentPoint last (A.map later argument))
        (function.app last.1 (arrow.val ≫ later.val)
          (domain.hom.app last (A.map later argument)))
    rw [domainLaw, functionLaw]
    exact (body.inv.naturality_apply (argumentArrow later argument) _).symm

set_option backward.isDefEq.respectTransparency false in
def sectionFunctionEquiv {A : DisplayedFamily P}
    {B : DisplayedFamily (totalSpace A)} {D E : Cᵒᵖ ⥤ Type u}
    (domain : A ≅ constantFamily P D)
    (body : B ≅ constantFamily (totalSpace A) E) (point : P.Elements) :
    DependentSection A (displayedToTotalElements A ⋙ B) point ≃
      (D.functorHom E).obj point.1 where
  toFun := sectionToFunction domain body point
  invFun := functionToSection domain body point
  left_inv witness := by
    apply DependentSection.ext
    intro target arrow argument
    rcases target with ⟨world, value⟩
    rcases arrow with ⟨change, follows⟩
    change point.1 ⟶ world at change
    change P.map change point.2 = value at follows
    subst value
    change A.obj (future point change) at argument
    change body.inv.app (argumentPoint (future point change) argument)
        (body.hom.app (argumentPoint (future point change)
          (domain.inv.app (future point change) (domain.hom.app (future point change) argument)))
          (witness.app (future point change) (futureArrow point change)
            (domain.inv.app (future point change)
              (domain.hom.app (future point change) argument)))) =
      witness.app (future point change) (futureArrow point change) argument
    have domainInverse := ConcreteCategory.congr_hom
      (domain.hom_inv_id_app (future point change)) argument
    change domain.inv.app (future point change)
      (domain.hom.app (future point change) argument) = argument at domainInverse
    rw [domainInverse]
    exact ConcreteCategory.congr_hom (body.hom_inv_id_app _) _
  right_inv function := by
    apply Functor.functorHom_ext
    intro world arrow
    apply ConcreteCategory.hom_ext
    intro argument
    change body.hom.app (argumentPoint (future point arrow)
        (domain.inv.app (future point arrow) argument))
        (body.inv.app (argumentPoint (future point arrow)
          (domain.inv.app (future point arrow) argument))
          (function.app world arrow
            (domain.hom.app (future point arrow) (domain.inv.app (future point arrow) argument)))) =
      function.app world arrow argument
    have domainInverse := ConcreteCategory.congr_hom
      (domain.inv_hom_id_app (future point arrow)) argument
    change domain.hom.app (future point arrow)
      (domain.inv.app (future point arrow) argument) = argument at domainInverse
    rw [domainInverse]
    exact ConcreteCategory.congr_hom (body.inv_hom_id_app _) _

def dependentReadout {A : DisplayedFamily P}
    {B : DisplayedFamily (totalSpace A)} {D E : Cᵒᵖ ⥤ Type u}
    (domain : A ≅ constantFamily P D)
    (body : B ≅ constantFamily (totalSpace A) E) (point : P.Elements)
    (witness : DependentSection A (displayedToTotalElements A ⋙ B) point)
    {world : Cᵒᵖ} (value : P.obj world) (arrow : point ⟶ ⟨world, value⟩)
    (argument : D.obj world) : E.obj world :=
  body.hom.app (argumentPoint ⟨world, value⟩
    (domain.inv.app ⟨world, value⟩ argument))
    (witness.app ⟨world, value⟩ arrow (domain.inv.app ⟨world, value⟩ argument))

theorem dependentReadout_congr {A : DisplayedFamily P}
    {B : DisplayedFamily (totalSpace A)} {D E : Cᵒᵖ ⥤ Type u}
    (domain : A ≅ constantFamily P D)
    (body : B ≅ constantFamily (totalSpace A) E) (point : P.Elements)
    (witness : DependentSection A (displayedToTotalElements A ⋙ B) point)
    {world : Cᵒᵖ} {first last : P.obj world} (same : first = last)
    (earlier : point ⟶ ⟨world, first⟩) (later : point ⟶ ⟨world, last⟩)
    (underlying : HEq earlier.val later.val) (argument : D.obj world) :
    dependentReadout domain body point witness first earlier argument =
      dependentReadout domain body point witness last later argument := by
  cases same
  have sameArrow : earlier = later := Subtype.ext (eq_of_heq underlying)
  cases sameArrow
  rfl

set_option backward.isDefEq.respectTransparency false in
def sectionFunctionIso {A : DisplayedFamily P}
    {B : DisplayedFamily (totalSpace A)} {D E : Cᵒᵖ ⥤ Type u}
    (domain : A ≅ constantFamily P D)
    (body : B ≅ constantFamily (totalSpace A) E) :
    dependentFunctions A (displayedToTotalElements A ⋙ B) ≅
      constantFamily P (D.functorHom E) := by
  refine NatIso.ofComponents (fun point => Equiv.toIso
    (sectionFunctionEquiv domain body point)) ?_
  intro first last arrow
  apply ConcreteCategory.hom_ext
  intro witness
  rcases first with ⟨world, value⟩
  rcases last with ⟨next, other⟩
  rcases arrow with ⟨change, follows⟩
  change world ⟶ next at change
  change P.map change value = other at follows
  subst other
  apply Functor.functorHom_ext
  intro final later
  apply ConcreteCategory.hom_ext
  intro argument
  change next ⟶ final at later
  change (sectionToFunction domain body ⟨next, P.map change value⟩
      (DependentSection.restrict A (displayedToTotalElements A ⋙ B)
        ⟨change, rfl⟩ witness)).app final later argument =
    (sectionToFunction domain body ⟨world, value⟩ witness).app final
      (change ≫ later) argument
  change body.hom.app (argumentPoint ⟨final, P.map later (P.map change value)⟩
      (domain.inv.app ⟨final, P.map later (P.map change value)⟩ argument))
      (witness.app ⟨final, P.map later (P.map change value)⟩
        (futureArrow ⟨world, value⟩ change ≫
          futureArrow (future ⟨world, value⟩ change) later)
        (domain.inv.app ⟨final, P.map later (P.map change value)⟩ argument)) =
    body.hom.app (argumentPoint ⟨final, P.map (change ≫ later) value⟩
      (domain.inv.app ⟨final, P.map (change ≫ later) value⟩ argument))
      (witness.app ⟨final, P.map (change ≫ later) value⟩
        ⟨change ≫ later, rfl⟩
        (domain.inv.app ⟨final, P.map (change ≫ later) value⟩ argument))
  exact dependentReadout_congr domain body (⟨world, value⟩ : P.Elements) witness
    (world := final) (first := P.map later (P.map change value))
    (last := P.map (change ≫ later) value)
    (P.map_comp_apply change later value).symm
    (futureArrow ⟨world, value⟩ change ≫
      futureArrow (future ⟨world, value⟩ change) later)
    (futureArrow ⟨world, value⟩ (change ≫ later)) (heq_of_eq rfl) argument

/-- Actual native product decoding agrees with the full presheaf function
object when its independently supplied decoded families are nondependent. -/
noncomputable def piFunctionIso (A : NativeType P)
    (B : NativeType (totalSpace A.decoded)) {D E : Cᵒᵖ ⥤ Type u}
    (domain : (show DisplayedFamily.{u,u,u,u} P from A.decoded) ≅ constantFamily P D)
    (body : (show DisplayedFamily.{u,u,u,u} (totalSpace A.decoded) from B.decoded) ≅
      constantFamily (totalSpace A.decoded) E) :
    (show DisplayedFamily.{u,u,u,u} P from (pi A B).decoded) ≅
      constantFamily P (D.functorHom E) :=
  piDecodeIso A B ≪≫
    (DependentProductNativeComparison.nativeIso
      (show DisplayedFamily.{u,u,u,u} P from A.decoded)).app
      (displayedToTotalElements (show DisplayedFamily.{u,u,u,u} P from A.decoded) ⋙
        (show DisplayedFamily.{u,u,u,u} (totalSpace A.decoded) from B.decoded)) ≪≫
    sectionFunctionIso domain body

set_option backward.isDefEq.respectTransparency false in
/-- Comprehension of a nondependent displayed family is the actual product
of its carrier and base, with values and reindexing retained. -/
def totalFamilyIso {A : DisplayedFamily P} {D : Cᵒᵖ ⥤ Type u}
    (family : A ≅ constantFamily P D) : totalSpace A ≅ D ⊗ P := by
  refine NatIso.ofComponents (fun world => Equiv.toIso {
    toFun := fun value => (family.hom.app ⟨world, value.1⟩ value.2, value.1)
    invFun := fun value => ⟨value.2, family.inv.app ⟨world, value.2⟩ value.1⟩
    left_inv := fun value => by
      change (Σ base : P.obj world, A.obj ⟨world, base⟩) at value
      rcases value with ⟨base, argument⟩
      exact congrArg (fun arg : A.obj ⟨world, base⟩ =>
        (⟨base, arg⟩ : (totalSpace A).obj world))
        (ConcreteCategory.congr_hom (family.hom_inv_id_app ⟨world, base⟩) argument)
    right_inv := fun value => by
      apply Prod.ext
      · change family.hom.app ⟨world, value.2⟩
          (family.inv.app ⟨world, value.2⟩ value.1) = value.1
        exact ConcreteCategory.congr_hom (family.inv_hom_id_app ⟨world, value.2⟩) value.1
      · rfl }) ?_
  intro first last arrow
  apply ConcreteCategory.hom_ext
  intro value
  apply Prod.ext
  · exact family.hom.naturality_apply (CategoryOfElements.homMk
      (F := P) ⟨first, value.1⟩ ⟨last, P.map arrow value.1⟩ arrow rfl) value.2
  · rfl

end Mettapedia.TypeTheory.NativeNondependentFunctionComparison
