import Mettapedia.CategoryTheory.QuantifiedClosedTheory
import Mettapedia.CategoryTheory.InternalConjunctiveObjectLawReflection
import Mettapedia.CategoryTheory.RelativeClosedBaseConservativity
import Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifierUniversalCells

/-!
# An independent quantifier-completion stage for a conjunctive closed theory

The initial presentation is the actual authored closed-base comparison
syntax. Its existing proposition object, truth and conjunction are retained
as original objects and arrows. The native interpretation is independently
constructed from the base operations. Its earned equivalence reflects the
four finite conjunctive diagrams, giving the stage required by the complete
quantifier closure. Raw formal contexts remain their original presentations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedQuantified

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open Mettapedia.GSLT.Core
open RelativeClosedSyntax GeneratedCategory
open RelativeClosedGeneratedQuantifier Iteration

universe k
variable (source : ConjunctiveClosedTheory.{k})

abbrev initialSignature := BaseComparisons.signature (C := source.closed.Obj)
abbrev proposition : Object (initialSignature source) :=
  baseObject (initialSignature source) source.operations.proposition

def truthRaw : RawHom (terminal (initialSignature source)) (proposition source) :=
  (BaseComparisons.inverseRaw (C := source.closed.Obj) .terminal).compose
    ⟨.base source.operations.truth, ⟨.baseArrow source.operations.truth⟩⟩

def conjunctionRaw : RawHom (product (proposition source) (proposition source)) (proposition source) :=
  (BaseComparisons.inverseRaw (C := source.closed.Obj)
    (.product source.operations.proposition source.operations.proposition)).compose
      ⟨.base source.operations.conjunction, ⟨.baseArrow source.operations.conjunction⟩⟩

def language : PredicateSyntax (initialSignature source) where
  proposition := proposition source
  conjunction := conjunctionRaw source

abbrev initialOperations := SourceOperations.operations (language source) (truthRaw source)
abbrev native := BaseComparisons.Conservativity.native (C := source.closed.Obj)
abbrev nativeAssignment := BaseComparisons.NativeDiagram.assignment (C := source.closed.Obj)
abbrev nativeRealization := BaseComparisons.NativeDiagram.realization (C := source.closed.Obj)

instance native_faithful : (native source).Faithful :=
  inferInstanceAs (BaseComparisons.Conservativity.equivalence (C := source.closed.Obj)).inverse.Faithful

theorem proposition_read : (native source).obj (proposition source) = source.operations.proposition :=
  RelativeClosedSyntax.Interpretation.functor_base_object (nativeAssignment source) (nativeRealization source) _

theorem unit_read : (native source).obj (terminal (initialSignature source)) = 𝟙_ source.closed.Obj :=
  RelativeClosedSyntax.Interpretation.functor_terminal_object (nativeAssignment source) (nativeRealization source)

theorem product_read :
    (native source).obj (product (proposition source) (proposition source)) =
      source.operations.proposition ⊗ source.operations.proposition :=
  (RelativeClosedSyntax.Interpretation.functor_product_object (nativeAssignment source)
    (nativeRealization source) (proposition source) (proposition source)).trans
      (congrArg₂ (fun first second : source.closed.Obj => first ⊗ second)
        (proposition_read source) (proposition_read source))

theorem truth_raw_read : RawInterpretation.Reads (nativeAssignment source) (truthRaw source)
    source.operations.truth :=
  ((nativeAssignment source).evaluate_compose (𝟙 (𝟙_ source.closed.Obj)) source.operations.truth rfl rfl).trans
    (congrArg (fun arrow : 𝟙_ source.closed.Obj ⟶ source.operations.proposition =>
      some (⟨𝟙_ source.closed.Obj, source.operations.proposition, arrow⟩ :
        RelativeClosedSyntax.Interpretation.ArrowValue source.closed.Obj))
      (Category.id_comp source.operations.truth))

theorem conjunction_raw_read : RawInterpretation.Reads (nativeAssignment source) (conjunctionRaw source)
    source.operations.conjunction :=
  ((nativeAssignment source).evaluate_compose
    (𝟙 (source.operations.proposition ⊗ source.operations.proposition)) source.operations.conjunction rfl rfl).trans
    (congrArg (fun arrow : source.operations.proposition ⊗ source.operations.proposition ⟶
        source.operations.proposition =>
      some (⟨source.operations.proposition ⊗ source.operations.proposition,
        source.operations.proposition, arrow⟩ : RelativeClosedSyntax.Interpretation.ArrowValue source.closed.Obj))
      (Category.id_comp source.operations.conjunction))

private theorem projection_read (second : Bool) :
    (native source).map (if second then GeneratedCategory.second (proposition source) (proposition source)
      else GeneratedCategory.first (proposition source) (proposition source)) ≫ eqToHom (proposition_read source) =
      eqToHom (product_read source) ≫
        (if second then snd source.operations.proposition source.operations.proposition
          else fst source.operations.proposition source.operations.proposition) := by
  cases second with
  | false =>
      change (native source).map (classOf (RawHom.first (proposition source) (proposition source))) ≫
        eqToHom (proposition_read source) = eqToHom (product_read source) ≫
          fst source.operations.proposition source.operations.proposition
      have complete := (conj_eqToHom_iff_heq
        ((native source).map (classOf (RawHom.first (proposition source) (proposition source))))
        (fst source.operations.proposition source.operations.proposition)
        (product_read source) (proposition_read source)).mpr
          (RelativeClosedSyntax.Interpretation.functor_map_heq (nativeAssignment source)
            (nativeRealization source) (RawHom.first (proposition source) (proposition source))
            (fst source.operations.proposition source.operations.proposition)
            ((nativeAssignment source).evaluate_first rfl rfl))
      simpa only [Category.assoc,
        eqToHom_trans, eqToHom_refl, Category.comp_id] using
        congrArg (fun arrow => arrow ≫ eqToHom (proposition_read source)) complete
  | true =>
      change (native source).map (classOf (RawHom.second (proposition source) (proposition source))) ≫
        eqToHom (proposition_read source) = eqToHom (product_read source) ≫
          snd source.operations.proposition source.operations.proposition
      have complete := (conj_eqToHom_iff_heq
        ((native source).map (classOf (RawHom.second (proposition source) (proposition source))))
        (snd source.operations.proposition source.operations.proposition)
        (product_read source) (proposition_read source)).mpr
          (RelativeClosedSyntax.Interpretation.functor_map_heq (nativeAssignment source)
            (nativeRealization source) (RawHom.second (proposition source) (proposition source))
            (snd source.operations.proposition source.operations.proposition)
            ((nativeAssignment source).evaluate_second rfl rfl))
      simpa only [Category.assoc,
        eqToHom_trans, eqToHom_refl, Category.comp_id] using
        congrArg (fun arrow => arrow ≫ eqToHom (proposition_read source)) complete

def nativePredicates : InternalConjunctiveObject.Map (initialOperations source) source.operations where
  functor := native source
  proposition := eqToIso (proposition_read source)
  truth := by
    have complete := (conj_eqToHom_iff_heq ((native source).map (classOf (truthRaw source)))
      source.operations.truth (unit_read source) (proposition_read source)).mpr
        (RelativeClosedSyntax.Interpretation.functor_map_heq (nativeAssignment source)
          (nativeRealization source) (truthRaw source) source.operations.truth (truth_raw_read source))
    change (native source).map (classOf (truthRaw source)) ≫ eqToHom (proposition_read source) = _
    rw [complete]
    simp only [eqToHom_refl, Category.comp_id]
    exact congrArg (fun arrow => arrow ≫ source.operations.truth) (toUnit_unique _ _)
  conjunction := by
    have complete := (conj_eqToHom_iff_heq ((native source).map (classOf (conjunctionRaw source)))
      source.operations.conjunction (product_read source) (proposition_read source)).mpr
        (RelativeClosedSyntax.Interpretation.functor_map_heq (nativeAssignment source)
          (nativeRealization source) (conjunctionRaw source) source.operations.conjunction (conjunction_raw_read source))
    have tuple : lift
        ((native source).map (GeneratedCategory.first (proposition source) (proposition source)) ≫
          eqToHom (proposition_read source))
        ((native source).map (GeneratedCategory.second (proposition source) (proposition source)) ≫
          eqToHom (proposition_read source)) = eqToHom (product_read source) := by
      apply CartesianMonoidalCategory.hom_ext
      · exact (lift_fst _ _).trans (projection_read source false)
      · exact (lift_snd _ _).trans (projection_read source true)
    change (native source).map (classOf (conjunctionRaw source)) ≫ eqToHom (proposition_read source) = _
    rw [complete]
    simp only [eqToHom_refl, Category.comp_id]
    exact congrArg (fun arrow => arrow ≫ source.operations.conjunction) tuple.symm

theorem initial_laws : (initialOperations source).Laws := by
  let : (nativePredicates source).functor.Faithful := native_faithful source
  exact (nativePredicates source).reflects_laws source.laws

def stage : Stage source.closed.Obj where
  symbols := BaseComparisons.symbols source.closed.Obj
  presentation := initialSignature source
  formed := BaseComparisons.headers
  language := language source
  truth := truthRaw source
  laws := initial_laws source

def freeObject : QuantifiedClosedTheory.{k} where
  closed := Closure.theory (stage source)
  operations := Closure.quantifiedOperations (stage := stage source)

end Mettapedia.CategoryTheory.RelativeClosedQuantified
