import Mettapedia.CategoryTheory.RelativeClosedInternalCategoryModelRealization
import Mettapedia.CategoryTheory.RelativeClosedInternalCategoryNativeCategory
import Mettapedia.CategoryTheory.InternalCategoryPresentedComparison
import Mettapedia.CategoryTheory.InternalCategoryFiniteLimitTransport
import Mettapedia.CategoryTheory.RelativeClosedSyntaxInterpretationReadout
import Mettapedia.CategoryTheory.InternalCategoryIso

/-!
# Complete readings of an extended generated category model

Restriction to the original category presentation supplies independently
computed generator readings. The matching-pair projections retain their
whole product-equalizer domain. These comparisons concern the actual extended
source category and an independently supplied target internal category.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedInternalCategory.ModelComparison

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open RelativeClosedSyntax GeneratedCategory Interpretation

universe k w z a l m

variable {C : Type k} [Category.{k} C] (vertex : C)
variable {D : Type w} [Category.{z} D] {symbols : Symbols.{a}}
variable {next : Signature (C := D) (symbols := symbols)}
variable (extension : SignatureMap (Presentation.signature vertex) next)
variable {E : Type l} [Category.{m} E] [CartesianMonoidalCategory E]
variable [MonoidalClosed E] [HasFiniteLimits E]
variable (base : C ⥤ E) (original : InternalCategory E)
variable (programComparison : base.obj vertex ≅ original.vertex)
variable (F : Object next ⥤ E)
variable (restriction : extension.functor ⋙ F = ModelRealization.functor vertex base original programComparison)

abbrev sourceCategory := NativeCategory.category vertex extension
abbrev meaning := ModelRealization.operations vertex base original programComparison

def value {first second : Object (Presentation.signature vertex)} (code : RawHom first second) : ArrowValue E :=
  ⟨F.obj (extension.object first), F.obj (extension.object second), F.map (classOf (extension.rawArrow code))⟩

include restriction in
theorem whole_restriction {first second : Object (Presentation.signature vertex)} (code : RawHom first second) :
    value vertex extension F code =
      ⟨(ModelRealization.functor vertex base original programComparison).obj first,
        (ModelRealization.functor vertex base original programComparison).obj second,
        (ModelRealization.functor vertex base original programComparison).map (classOf code)⟩ :=
  congrArg (fun route : Object (Presentation.signature vertex) ⥤ E =>
    (⟨route.obj first,route.obj second,route.map (classOf code)⟩ : ArrowValue E)) restriction

include restriction in
theorem whole_source : value vertex extension F (ModelRealization.sourceCode vertex) =
    ⟨original.edge,base.obj vertex,original.source ≫ programComparison.inv⟩ :=
  (whole_restriction vertex extension base original programComparison F restriction _).trans
    (ModelRealization.complete_generated_source vertex base original programComparison)

include restriction in
theorem whole_target : value vertex extension F (ModelRealization.targetCode vertex) =
    ⟨original.edge,base.obj vertex,original.target ≫ programComparison.inv⟩ :=
  (whole_restriction vertex extension base original programComparison F restriction _).trans
    (ModelRealization.complete_generated_target vertex base original programComparison)

include restriction in
theorem whole_unit : value vertex extension F (ModelRealization.unitCode vertex) =
    ⟨base.obj vertex,original.edge,programComparison.hom ≫ original.unit⟩ :=
  (whole_restriction vertex extension base original programComparison F restriction _).trans
    (ModelRealization.complete_generated_unit vertex base original programComparison)

include restriction in
theorem whole_composition : value vertex extension F (ModelRealization.compositionCode vertex) =
    ⟨(meaning vertex base original programComparison).toGraph.composable,original.edge,
      (meaning vertex base original programComparison).composition⟩ :=
  (whole_restriction vertex extension base original programComparison F restriction _).trans
    (ModelRealization.complete_generated_composition vertex base original programComparison)

def firstCode := (Presentation.inclusion vertex).rawArrow (Endpoints.first vertex)
def secondCode := (Presentation.inclusion vertex).rawArrow (Endpoints.second vertex)

theorem generated_first :
    (⟨(ModelRealization.functor vertex base original programComparison).obj (ModelRealization.compositionSource vertex),
      (ModelRealization.functor vertex base original programComparison).obj (ModelRealization.edgeObject vertex),
      (ModelRealization.functor vertex base original programComparison).map (classOf (firstCode vertex))⟩ : ArrowValue E) =
      ⟨(meaning vertex base original programComparison).toGraph.composable,original.edge,
        (meaning vertex base original programComparison).toGraph.first⟩ := by
  have complete := functor_complete_readout (ModelRealization.assignment vertex base original programComparison)
    (ModelRealization.realization vertex base original programComparison) (firstCode vertex)
  have actual := (EquationExtension.evaluate_arrow_original (endpointSignature vertex)
    (Presentation.declaration vertex)
    (EquationReadout.assignment vertex base (meaning vertex base original programComparison))
    (Endpoints.first vertex).code).trans
      (EquationReadout.first_read vertex base (meaning vertex base original programComparison))
  exact Option.some.inj (complete.symm.trans actual)

theorem generated_second :
    (⟨(ModelRealization.functor vertex base original programComparison).obj (ModelRealization.compositionSource vertex),
      (ModelRealization.functor vertex base original programComparison).obj (ModelRealization.edgeObject vertex),
      (ModelRealization.functor vertex base original programComparison).map (classOf (secondCode vertex))⟩ : ArrowValue E) =
      ⟨(meaning vertex base original programComparison).toGraph.composable,original.edge,
        (meaning vertex base original programComparison).toGraph.second⟩ := by
  have complete := functor_complete_readout (ModelRealization.assignment vertex base original programComparison)
    (ModelRealization.realization vertex base original programComparison) (secondCode vertex)
  have actual := (EquationExtension.evaluate_arrow_original (endpointSignature vertex)
    (Presentation.declaration vertex)
    (EquationReadout.assignment vertex base (meaning vertex base original programComparison))
    (Endpoints.second vertex).code).trans
      (EquationReadout.second_read vertex base (meaning vertex base original programComparison))
  exact Option.some.inj (complete.symm.trans actual)

include restriction in
theorem whole_first : value vertex extension F (firstCode vertex) =
    ⟨(meaning vertex base original programComparison).toGraph.composable,original.edge,
      (meaning vertex base original programComparison).toGraph.first⟩ :=
  (whole_restriction vertex extension base original programComparison F restriction _).trans
    (generated_first vertex base original programComparison)

include restriction in
theorem whole_second : value vertex extension F (secondCode vertex) =
    ⟨(meaning vertex base original programComparison).toGraph.composable,original.edge,
      (meaning vertex base original programComparison).toGraph.second⟩ :=
  (whole_restriction vertex extension base original programComparison F restriction _).trans
    (generated_second vertex base original programComparison)

include restriction in
theorem vertices_same : F.obj (sourceCategory vertex extension).vertex = base.obj vertex :=
  congrArg ArrowValue.target (whole_source vertex extension base original programComparison F restriction)

include restriction in
theorem edges_same : F.obj (sourceCategory vertex extension).edge = original.edge :=
  congrArg ArrowValue.source (whole_source vertex extension base original programComparison F restriction)

def vertexComparison : F.obj (sourceCategory vertex extension).vertex ≅ original.vertex :=
  (eqToIso (vertices_same vertex extension base original programComparison F restriction)).trans programComparison

def edgeComparison : F.obj (sourceCategory vertex extension).edge ≅ original.edge :=
  eqToIso (edges_same vertex extension base original programComparison F restriction)

include restriction in
theorem pairs_same : F.obj (NativeCategory.endpoints vertex extension).pair.pt =
    (meaning vertex base original programComparison).toGraph.composable :=
  congrArg ArrowValue.source (whole_composition vertex extension base original programComparison F restriction)

def pairComparison : F.obj (NativeCategory.endpoints vertex extension).pair.pt ≅
    (meaning vertex base original programComparison).toGraph.composable :=
  eqToIso (pairs_same vertex extension base original programComparison F restriction)

theorem source_square :
    (edgeComparison vertex extension base original programComparison F restriction).hom ≫ original.source =
      F.map (sourceCategory vertex extension).source ≫
        (vertexComparison vertex extension base original programComparison F restriction).hom := by
  have actual := (conj_eqToHom_iff_heq _ _
    (edges_same vertex extension base original programComparison F restriction)
    (vertices_same vertex extension base original programComparison F restriction)).mpr
      (ArrowValue.arrows_heq (whole_source vertex extension base original programComparison F restriction))
  erw [actual]
  simp only [edgeComparison, vertexComparison, Iso.trans_hom, eqToIso, Category.assoc,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  erw [Iso.inv_hom_id, Category.comp_id]

theorem target_square :
    (edgeComparison vertex extension base original programComparison F restriction).hom ≫ original.target =
      F.map (sourceCategory vertex extension).target ≫
        (vertexComparison vertex extension base original programComparison F restriction).hom := by
  have actual := (conj_eqToHom_iff_heq _ _
    (edges_same vertex extension base original programComparison F restriction)
    (vertices_same vertex extension base original programComparison F restriction)).mpr
      (ArrowValue.arrows_heq (whole_target vertex extension base original programComparison F restriction))
  erw [actual]
  simp only [edgeComparison, vertexComparison, Iso.trans_hom, eqToIso, Category.assoc,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  erw [Iso.inv_hom_id, Category.comp_id]

theorem unit_square : F.map (sourceCategory vertex extension).unit ≫
    (edgeComparison vertex extension base original programComparison F restriction).hom =
      (vertexComparison vertex extension base original programComparison F restriction).hom ≫ original.unit := by
  have actual := (conj_eqToHom_iff_heq _ _
    (vertices_same vertex extension base original programComparison F restriction)
    (edges_same vertex extension base original programComparison F restriction)).mpr
      (ArrowValue.arrows_heq (whole_unit vertex extension base original programComparison F restriction))
  erw [actual]
  simp only [edgeComparison, vertexComparison, Iso.trans_hom, eqToIso, Category.assoc,
    eqToHom_trans, eqToHom_refl, Category.comp_id]

theorem raw_composition_square : F.map (NativeCategory.endpoints vertex extension).composition ≫
    (edgeComparison vertex extension base original programComparison F restriction).hom =
      (pairComparison vertex extension base original programComparison F restriction).hom ≫
        (meaning vertex base original programComparison).composition := by
  have actual := (conj_eqToHom_iff_heq _ _
    (pairs_same vertex extension base original programComparison F restriction)
    (edges_same vertex extension base original programComparison F restriction)).mpr
      (ArrowValue.arrows_heq (whole_composition vertex extension base original programComparison F restriction))
  erw [actual]
  simp only [edgeComparison, pairComparison, eqToIso, Category.assoc,
    eqToHom_trans, eqToHom_refl, Category.comp_id]

theorem raw_first_square : F.map (NativeCategory.endpoints vertex extension).pair.fst ≫
    (edgeComparison vertex extension base original programComparison F restriction).hom =
      (pairComparison vertex extension base original programComparison F restriction).hom ≫
        (meaning vertex base original programComparison).toGraph.first := by
  have actual := (conj_eqToHom_iff_heq _ _
    (pairs_same vertex extension base original programComparison F restriction)
    (edges_same vertex extension base original programComparison F restriction)).mpr
      (ArrowValue.arrows_heq (whole_first vertex extension base original programComparison F restriction))
  erw [actual]
  simp only [edgeComparison, pairComparison, eqToIso, Category.assoc,
    eqToHom_trans, eqToHom_refl, Category.comp_id]

theorem raw_second_square : F.map (NativeCategory.endpoints vertex extension).pair.snd ≫
    (edgeComparison vertex extension base original programComparison F restriction).hom =
      (pairComparison vertex extension base original programComparison F restriction).hom ≫
        (meaning vertex base original programComparison).toGraph.second := by
  have actual := (conj_eqToHom_iff_heq _ _
    (pairs_same vertex extension base original programComparison F restriction)
    (edges_same vertex extension base original programComparison F restriction)).mpr
      (ArrowValue.arrows_heq (whole_second vertex extension base original programComparison F restriction))
  erw [actual]
  simp only [edgeComparison, pairComparison, eqToIso, Category.assoc,
    eqToHom_trans, eqToHom_refl, Category.comp_id]

def semanticPair : (meaning vertex base original programComparison).toGraph.composable ⟶
    original.toInternalGraph.Composable :=
  pullback.lift (meaning vertex base original programComparison).toGraph.first
    (meaning vertex base original programComparison).toGraph.second
    (InternalCategoryVertexIso.matching original programComparison _ _
      (CartesianEqualizerPullback.condition
        (meaning vertex base original programComparison).target
        (meaning vertex base original programComparison).source))

omit [MonoidalClosed E] in
theorem semantic_composition : (meaning vertex base original programComparison).composition =
    semanticPair vertex base original programComparison ≫ original.composition := by
  exact InternalCategoryVertexIso.complete_compose_read original programComparison _ _ _

variable [PreservesLimitsOfShape WalkingCospan F]

abbrev mappedEndpoints := InternalCategoryFiniteLimitTransport.endpoints F (sourceCategory vertex extension)

def pairMap := InternalCategoryPresentedComparison.pairMap (mappedEndpoints vertex extension F) original
  (vertexComparison vertex extension base original programComparison F restriction).hom
  (edgeComparison vertex extension base original programComparison F restriction).hom
  (source_square vertex extension base original programComparison F restriction)
  (target_square vertex extension base original programComparison F restriction)

def sourcePairLift : (sourceCategory vertex extension).toInternalGraph.Composable ⟶
    (NativeCategory.endpoints vertex extension).pair.pt :=
  InternalCategoryPresentedDiagrams.pairLift (NativeCategory.endpoints vertex extension)
    (pullback.fst _ _) (pullback.snd _ _) pullback.condition

theorem complete_pair_map : F.map (sourcePairLift vertex extension) ≫
    (pairComparison vertex extension base original programComparison F restriction).hom ≫
      semanticPair vertex base original programComparison =
        pairMap vertex extension base original programComparison F restriction := by
  apply pullback.hom_ext
  · simp only [Category.assoc, semanticPair, pullback.lift_fst]
    rw [← raw_first_square, ← Category.assoc, ← F.map_comp]
    rw [sourcePairLift, PullbackCone.IsLimit.lift_fst]
    exact (InternalCategoryPresentedComparison.pairMap_first
      (mappedEndpoints vertex extension F) original
      (vertexComparison vertex extension base original programComparison F restriction).hom
      (edgeComparison vertex extension base original programComparison F restriction).hom
      (source_square vertex extension base original programComparison F restriction)
      (target_square vertex extension base original programComparison F restriction)).symm
  · simp only [Category.assoc, semanticPair, pullback.lift_snd]
    rw [← raw_second_square, ← Category.assoc, ← F.map_comp]
    rw [sourcePairLift, PullbackCone.IsLimit.lift_snd]
    exact (InternalCategoryPresentedComparison.pairMap_second
      (mappedEndpoints vertex extension F) original
      (vertexComparison vertex extension base original programComparison F restriction).hom
      (edgeComparison vertex extension base original programComparison F restriction).hom
      (source_square vertex extension base original programComparison F restriction)
      (target_square vertex extension base original programComparison F restriction)).symm

theorem composition_square : F.map (sourceCategory vertex extension).composition ≫
    (edgeComparison vertex extension base original programComparison F restriction).hom =
      pairMap vertex extension base original programComparison F restriction ≫ original.composition := by
  change F.map (sourcePairLift vertex extension ≫ (NativeCategory.endpoints vertex extension).composition) ≫ _ = _
  rw [F.map_comp, Category.assoc, raw_composition_square, semantic_composition]
  rw [← Category.assoc, ← Category.assoc]
  have actual := congrArg (fun arrow => arrow ≫ original.composition)
    (complete_pair_map vertex extension base original programComparison F restriction)
  simpa only [Category.assoc] using actual

def hom : InternalCategory.Hom
    (InternalCategoryFiniteLimitTransport.category F (sourceCategory vertex extension)) original :=
  InternalCategoryPresentedComparison.hom (mappedEndpoints vertex extension F) original
    (vertexComparison vertex extension base original programComparison F restriction).hom
    (edgeComparison vertex extension base original programComparison F restriction).hom
    (source_square vertex extension base original programComparison F restriction)
    (target_square vertex extension base original programComparison F restriction)
    (InternalCategoryFiniteLimitTransport.triples F (sourceCategory vertex extension))
    (InternalCategoryFiniteLimitTransport.tripleLimit F (sourceCategory vertex extension))
    (InternalCategoryFiniteLimitTransport.laws F (sourceCategory vertex extension))
    (unit_square vertex extension base original programComparison F restriction)
    (composition_square vertex extension base original programComparison F restriction)

def comparison : InternalCategoryFiniteLimitTransport.category F (sourceCategory vertex extension) ≅ original :=
  InternalCategoryIso.iso (hom vertex extension base original programComparison F restriction)
    (vertexComparison vertex extension base original programComparison F restriction)
    (edgeComparison vertex extension base original programComparison F restriction) rfl rfl

theorem complete_identity :
    (InternalCategoryFiniteLimitTransport.category F (sourceCategory vertex extension)).unit ≫
      (comparison vertex extension base original programComparison F restriction).hom.edge =
      (comparison vertex extension base original programComparison F restriction).hom.vertex ≫ original.unit :=
  (comparison vertex extension base original programComparison F restriction).hom.unit

theorem complete_chosen_composition :
    (InternalCategoryFiniteLimitTransport.category F (sourceCategory vertex extension)).composition ≫
      (comparison vertex extension base original programComparison F restriction).hom.edge =
      (comparison vertex extension base original programComparison F restriction).hom.toHom.composableMap ≫
        original.composition :=
  (comparison vertex extension base original programComparison F restriction).hom.composition

theorem complete_matching_readout {stage : Object next}
    (before after : stage ⟶ (sourceCategory vertex extension).edge)
    (matching : before ≫ (sourceCategory vertex extension).target =
      after ≫ (sourceCategory vertex extension).source) :
    F.map ((sourceCategory vertex extension).compose before after matching) ≫
      (comparison vertex extension base original programComparison F restriction).hom.edge =
      original.compose
        (F.map before ≫ (comparison vertex extension base original programComparison F restriction).hom.edge)
        (F.map after ≫ (comparison vertex extension base original programComparison F restriction).hom.edge)
        (by
          erw [Category.assoc, (comparison vertex extension base original programComparison F restriction).hom.target,
            ← Category.assoc, ← F.map_comp, matching, F.map_comp, Category.assoc,
            ← (comparison vertex extension base original programComparison F restriction).hom.source, ← Category.assoc]) := by
  have actual := (comparison vertex extension base original programComparison F restriction).hom.compose_readout
    (F.map before) (F.map after)
    (InternalCategoryFiniteLimitTransport.mapped_matching F (sourceCategory vertex extension) before after matching)
  rw [InternalCategoryFiniteLimitTransport.category_compose_read] at actual
  exact actual

end Mettapedia.CategoryTheory.RelativeClosedInternalCategory.ModelComparison
