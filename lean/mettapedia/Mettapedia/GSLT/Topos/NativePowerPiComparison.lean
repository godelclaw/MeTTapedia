import Mettapedia.GSLT.Topos.NativePowerPredicates
import Mettapedia.TypeTheory.NativeLocalTypeFormers
import Mettapedia.TypeTheory.PresheafNativePropositionReadout

/-!
# Ordinary native products and local function objects

The dependent-product adjunction over an independently varying parameter
context, with a constant argument presheaf and a constant codomain presheaf,
recovers the complete local function object. The comparison retains every
future argument and commutes with evaluation.
-/

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.Topos.NativePowerPiComparison

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open DisplayedPresheafTransport DisplayedPresheafComprehension
open DisplayedPresheafParameterFamilies DisplayedPresheafPi DisplayedPresheafSlicePi
open DisplayedPresheafSliceSubstitution
open ConstructivePresheaf

universe u
variable {C : Type u} [Category.{u} C]
variable (P A B : Cᵒᵖ ⥤ Type u)

abbrev domain := parameterFamily P A
abbrev codomain := parameterFamily (totalSpace (domain P A)) B
noncomputable abbrev dependent := piDisplayed (domain P A) (codomain P A B)
abbrev ordinary := parameterFamily P (functions A B)

private theorem arrow_heq {Q : Cᵒᵖ ⥤ Type u} (source : Q.Elements) (future : Cᵒᵖ)
    {first second : Q.obj future} (same : first = second) (arrow : source.1 ⟶ future)
    (left : Q.map arrow source.2 = first) (right : Q.map arrow source.2 = second) :
    HEq (CategoryOfElements.homMk source ⟨future, first⟩ arrow left)
      (CategoryOfElements.homMk source ⟨future, second⟩ arrow right) := by
  cases same
  rfl

private theorem mapped_heq {D : Type u} [Category.{u} D] (F : D ⥤ Type u)
    {source first second : D} (same : first = second)
    (left : source ⟶ first) (right : source ⟶ second) (arrows : HEq left right)
    (value : F.obj source) : HEq (F.map left value) (F.map right value) := by
  cases same
  cases arrows
  rfl

private theorem evaluated_heq (P A B : Cᵒᵖ ⥤ Type u)
    {first second : (totalSpace (domain P A)).Elements} (same : first = second)
    {left : (dependent P A B).obj ((totalProjection (domain P A)).mapElements.obj first)}
    {right : (dependent P A B).obj ((totalProjection (domain P A)).mapElements.obj second)}
    (values : HEq left right) :
    HEq (((displayedProductAdjunction (domain P A)).counit.app (codomain P A B)).app first left)
      (((displayedProductAdjunction (domain P A)).counit.app (codomain P A B)).app second right) := by
  cases same
  cases values
  rfl

/-- The ordinary function object supplies an actual dependent body. -/
def body : reindexDisplayed (totalProjection (domain P A)) (ordinary P A B) ⟶
    codomain P A B where
  app point := TypeCat.ofHom fun function => function.app point.1 (𝟙 point.1) point.2.2
  naturality := by
    intro source target arrow
    apply ConcreteCategory.hom_ext
    intro function
    have coordinates := congrArg (fun pair : (totalSpace (domain P A)).obj target.1 =>
      (show A.obj target.1 from pair.2)) arrow.property
    change A.map arrow.val source.2.2 = target.2.2 at coordinates
    change function.app target.1 (arrow.val ≫ 𝟙 target.1) target.2.2 =
      B.map arrow.val (function.app source.1 (𝟙 source.1) source.2.2)
    rw [coordinates.symm, Category.comp_id]
    have natural := ConcreteCategory.congr_hom (function.naturality arrow.val (𝟙 source.1))
      source.2.2
    change function.app target.1 (𝟙 source.1 ≫ arrow.val)
      (A.map arrow.val source.2.2) = B.map arrow.val
        (function.app source.1 (𝟙 source.1) source.2.2) at natural
    erw [Category.id_comp] at natural
    exact natural

/-- Transpose the ordinary evaluator through the existing native Π adjunction. -/
noncomputable def intoDependent : ordinary P A B ⟶ dependent P A B :=
  (displayedProductAdjunction (domain P A)).homEquiv (ordinary P A B) (codomain P A B)
    (body P A B)

theorem intoDependent_evaluation :
    (reindexFunctor (totalProjection (domain P A))).map (intoDependent P A B) ≫
      (displayedProductAdjunction (domain P A)).counit.app (codomain P A B) = body P A B :=
  ((displayedProductAdjunction (domain P A)).homEquiv _ _).symm_apply_apply _

/-- Read a dependent function at a supplied future argument. -/
noncomputable def read (point : P.Elements) (function : (dependent P A B).obj point)
    (future : Cᵒᵖ) (restriction : point.1 ⟶ future) (argument : A.obj future) : B.obj future :=
  ((displayedProductAdjunction (domain P A)).counit.app (codomain P A B)).app
    ⟨future, ⟨P.map restriction point.2, argument⟩⟩
    ((dependent P A B).map (CategoryOfElements.homMk _ _ restriction rfl) function)

noncomputable def outFunction (point : P.Elements)
    (function : (dependent P A B).obj point) : (functions A B).obj point.1 where
  app future restriction := TypeCat.ofHom (read P A B point function future restriction)
  naturality := by
    intro future target arrow restriction
    change point.1 ⟶ future at restriction
    apply ConcreteCategory.hom_ext
    intro argument
    let first : (totalSpace (domain P A)).Elements :=
      ⟨future, ⟨P.map restriction point.2, argument⟩⟩
    let last : (totalSpace (domain P A)).Elements :=
      ⟨target, ⟨P.map (restriction ≫ arrow) point.2, A.map arrow argument⟩⟩
    let step : first ⟶ last := CategoryOfElements.homMk _ _ arrow (by
      apply Sigma.ext
      · exact (P.map_comp_apply restriction arrow point.2).symm
      · rfl)
    have natural := ((displayedProductAdjunction (domain P A)).counit.app
      (codomain P A B)).naturality_apply step
      ((dependent P A B).map (CategoryOfElements.homMk _ _ restriction rfl) function)
    change _ = B.map arrow (read P A B point function future restriction argument) at natural
    change read P A B point function target (restriction ≫ arrow) (A.map arrow argument) = _
    have composite :
        (CategoryOfElements.homMk point ⟨target, P.map (restriction ≫ arrow) point.2⟩
          (restriction ≫ arrow) rfl) =
        CategoryOfElements.homMk point ⟨future, P.map restriction point.2⟩ restriction rfl ≫
          (totalProjection (domain P A)).mapElements.map step := by
      apply Subtype.ext
      rfl
    unfold read
    change ((displayedProductAdjunction (domain P A)).counit.app (codomain P A B)).app
      last ((dependent P A B).map (CategoryOfElements.homMk point
        ⟨target, P.map (restriction ≫ arrow) point.2⟩ (restriction ≫ arrow) rfl) function) =
      B.map arrow (read P A B point function future restriction argument)
    rw [composite, (dependent P A B).map_comp_apply]
    exact natural

noncomputable def fromDependent : dependent P A B ⟶ ordinary P A B where
  app point := TypeCat.ofHom (outFunction P A B point)
  naturality := by
    rintro ⟨first, value⟩ ⟨last, lastValue⟩ ⟨step, follows⟩
    change first ⟶ last at step
    change P.map step value = lastValue at follows
    subst lastValue
    apply ConcreteCategory.hom_ext
    intro function
    apply Functor.HomObj.ext
    funext future restriction
    change last ⟶ future at restriction
    apply ConcreteCategory.hom_ext
    intro argument
    change read P A B ⟨last, P.map step value⟩
        ((dependent P A B).map ⟨step, rfl⟩ function) future restriction argument =
      read P A B ⟨first, value⟩ function future (step ≫ restriction) argument
    let leftPoint : (totalSpace (domain P A)).Elements :=
      ⟨future, ⟨P.map restriction (P.map step value), argument⟩⟩
    let rightPoint : (totalSpace (domain P A)).Elements :=
      ⟨future, ⟨P.map (step ≫ restriction) value, argument⟩⟩
    have pointEquality := P.map_comp_apply step restriction value
    have points : leftPoint = rightPoint := by
      apply congrArg (fun base => (⟨future, ⟨base, argument⟩⟩ :
        (totalSpace (domain P A)).Elements))
      exact pointEquality.symm
    let next : @Quiver.Hom P.Elements inferInstance ⟨last, P.map step value⟩
        ((totalProjection (domain P A)).mapElements.obj leftPoint) :=
      CategoryOfElements.homMk _ _ restriction rfl
    let start : @Quiver.Hom P.Elements inferInstance ⟨first, value⟩
        ⟨last, P.map step value⟩ := ⟨step, rfl⟩
    let direct : @Quiver.Hom P.Elements inferInstance ⟨first, value⟩
        ((totalProjection (domain P A)).mapElements.obj rightPoint) :=
      CategoryOfElements.homMk _ _ (step ≫ restriction) rfl
    have arrows : HEq (start ≫ next) direct :=
      arrow_heq (⟨first, value⟩ : P.Elements) future pointEquality.symm
        (step ≫ restriction) pointEquality rfl
    have values := mapped_heq (dependent P A B)
      (congrArg (fun point => (totalProjection (domain P A)).mapElements.obj point) points)
      (start ≫ next) direct arrows function
    have evaluated := evaluated_heq P A B points values
    have composed := (dependent P A B).map_comp_apply start next function
    change ((displayedProductAdjunction (domain P A)).counit.app (codomain P A B)).app
      leftPoint ((dependent P A B).map next ((dependent P A B).map start function)) = _
    rw [← composed]
    exact eq_of_heq evaluated

/-- The readback agrees with the original dependent counit at every argument. -/
theorem fromDependent_evaluation :
    (reindexFunctor (totalProjection (domain P A))).map (fromDependent P A B) ≫
      body P A B =
        (displayedProductAdjunction (domain P A)).counit.app (codomain P A B) := by
  ext point function
  change read P A B ⟨point.1, point.2.1⟩ function point.1 (𝟙 point.1) point.2.2 = _
  let futurePoint : (totalSpace (domain P A)).Elements :=
    ⟨point.1, ⟨P.map (𝟙 point.1) point.2.1, point.2.2⟩⟩
  have points : futurePoint = point := by
    rcases point with ⟨world, base, argument⟩
    change (⟨world, ⟨P.map (𝟙 world) base, argument⟩⟩ :
      (totalSpace (domain P A)).Elements) = ⟨world, ⟨base, argument⟩⟩
    congr 2
    exact P.map_id_apply world base
  let source : P.Elements := ⟨point.1, point.2.1⟩
  let arrow : source ⟶ (show P.Elements from (totalProjection (domain P A)).mapElements.obj futurePoint) :=
    CategoryOfElements.homMk _ _ (𝟙 point.1) rfl
  have arrows : HEq arrow (𝟙 source) :=
    arrow_heq source point.1 (P.map_id_apply _ _) (𝟙 point.1) rfl (P.map_id_apply _ _)
  have values := mapped_heq (dependent P A B)
    (congrArg (fun point => (totalProjection (domain P A)).mapElements.obj point) points)
    arrow (𝟙 source) arrows function
  have evaluated := evaluated_heq P A B points values
  have identity := (dependent P A B).map_id_apply source function
  change read P A B source function point.1 (𝟙 point.1) point.2.2 = _
  exact (eq_of_heq evaluated).trans (congrArg
    (((displayedProductAdjunction (domain P A)).counit.app (codomain P A B)).app point)
    identity)

theorem dependent_roundtrip : fromDependent P A B ≫ intoDependent P A B = 𝟙 _ := by
  apply ((displayedProductAdjunction (domain P A)).homEquiv _ _).symm.injective
  change (reindexFunctor (totalProjection (domain P A))).map
      (fromDependent P A B ≫ intoDependent P A B) ≫ _ =
    (reindexFunctor (totalProjection (domain P A))).map (𝟙 _) ≫ _
  rw [Functor.map_comp, Category.assoc, intoDependent_evaluation, fromDependent_evaluation]
  simp

theorem ordinary_roundtrip : intoDependent P A B ≫ fromDependent P A B = 𝟙 _ := by
  ext point function
  apply Functor.HomObj.ext
  funext future restriction
  change point.1 ⟶ future at restriction
  apply ConcreteCategory.hom_ext
  intro argument
  have evaluated := ConcreteCategory.congr_hom
    (NatTrans.congr_app (intoDependent_evaluation P A B)
      ⟨future, ⟨P.map restriction point.2, argument⟩⟩)
    ((functions A B).map restriction function)
  have natural := (intoDependent P A B).naturality_apply
    (CategoryOfElements.homMk point ⟨future, P.map restriction point.2⟩ restriction rfl)
    function
  change ((displayedProductAdjunction (domain P A)).counit.app (codomain P A B)).app
      ⟨future, ⟨P.map restriction point.2, argument⟩⟩
      ((intoDependent P A B).app ⟨future, P.map restriction point.2⟩
        ((functions A B).map restriction function)) =
    function.app future (restriction ≫ 𝟙 future) argument at evaluated
  change read P A B point ((intoDependent P A B).app point function) future restriction argument =
    function.app future restriction argument
  unfold read
  change ((displayedProductAdjunction (domain P A)).counit.app (codomain P A B)).app
      ⟨future, ⟨P.map restriction point.2, argument⟩⟩
      ((dependent P A B).map (CategoryOfElements.homMk point
        ⟨future, P.map restriction point.2⟩ restriction rfl)
        ((intoDependent P A B).app point function)) = _
  rw [← natural]
  erw [Category.comp_id] at evaluated
  exact evaluated

/-- The isomorphism is earned from both evaluator roundtrips. -/
noncomputable def comparison : ordinary P A B ≅ dependent P A B where
  hom := intoDependent P A B
  inv := fromDependent P A B
  hom_inv_id := ordinary_roundtrip P A B
  inv_hom_id := dependent_roundtrip P A B

open NativeLocalTypeFormers PresheafNativePropositionReadout DisplayedPresheafClassifier
open NativePowerPredicates

theorem propositions_constant (P : Cᵒᵖ ⥤ Type u) :
    propositions P = parameterFamily P (omegaFunctor (C := C)) := by
  refine Functor.hext (fun _ => rfl) ?_
  intro source target arrow
  rfl

/-- The chosen native Π representative decodes to the genuine local power
family. Only the independently checked argument-family comparison is used. -/
noncomputable def nativeComparison (native : NativeType P)
    (constant : native.decoded = domain P A) :
    ordinary P A (omegaFunctor (C := C)) ≅
      (NativeLocalTypeFormers.pi native (nativeOmega (totalSpace native.decoded))).decoded := by
  have former :
      piDisplayed native.decoded (nativeOmega (totalSpace native.decoded)).decoded =
        dependent P A (omegaFunctor (C := C)) := by
    rw [nativeOmega_decode, propositions_constant]
    exact congrArg (fun family : DisplayedFamily P =>
      piDisplayed family (parameterFamily (totalSpace family) (omegaFunctor (C := C)))) constant
  exact comparison P A (omegaFunctor (C := C)) ≪≫ (eqToIso former).symm ≪≫
    (NativeLocalTypeFormers.piDecodeIso native (nativeOmega (totalSpace native.decoded))).symm

/-- Every native product component is compared with a complete local predicate,
including all future arguments; this is not a global-section comparison. -/
noncomputable def nativeComponent (native : NativeType P)
    (constant : native.decoded = domain P A) (point : P.Elements) :
    (NativeLocalTypeFormers.pi native (nativeOmega (totalSpace native.decoded))).decoded.obj point ≃
      (power A).obj point.1 :=
  ((nativeComparison P A native constant).app point).toEquiv.symm

end Mettapedia.GSLT.Topos.NativePowerPiComparison
