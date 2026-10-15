import Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifierNativeIteration
import Mettapedia.CategoryTheory.RelativeClosedPredicateLogicOperations
import Mettapedia.GSLT.Core.RelativeClosedGeneratedQuantifierControls

/-!
# Actual second-stage quantification of a first-stage quantifier

The initial stage is the independent program, predicate, modal and structural
presentation. Its four conjunctive diagrams are inherited from the authored
logical source. The first generated existential along a structural image is
then itself the complete route of the second stage. Both quotient images
are retained, with their full function inputs, changing parameters and
empty-fibre rejection. The proposition name is retained at every depth.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedGeneratedQuantifierIterationControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open Mettapedia.CategoryTheory RelativeClosedSyntax GeneratedCategory
open HigherOrderInternalPredicateObject HigherOrderInternalPredicateQuantifier
open ElementaryTypePredicateReadout
open PositionedRewritePredicatePower (name family_name)


def lawfulMap :=
  ((RelativeClosedPositionedModalPresentation.arrowInclusion RelativeClosedGeneratedQuantifierControls.source RelativeClosedGeneratedQuantifierControls.selection).compose
    (RelativeClosedPositionedModalPresentation.definingInclusion RelativeClosedGeneratedQuantifierControls.source RelativeClosedGeneratedQuantifierControls.selection)).compose
    (RelativeClosedStructuralImagePresentation.inclusion RelativeClosedGeneratedQuantifierControls.source RelativeClosedGeneratedQuantifierControls.selection RelativeClosedGeneratedQuantifierControls.constructors)

def logicalLanguage : RelativeClosedGeneratedQuantifier.PredicateSyntax (RelativeClosedPredicateLogic.lawfulSignature (C := RelativeClosedGeneratedQuantifierControls.source.closed.Obj)) where
  proposition := RelativeClosedPredicateLogic.equationInclusion.object RelativeClosedPredicateLogic.omega
  conjunction := RelativeClosedPredicateLogic.equationInclusion.rawArrow RelativeClosedPredicateLogic.conjunctionRaw

def logicalTruth :=
  (RelativeClosedPredicateLogic.equationInclusion
    (C := RelativeClosedGeneratedQuantifierControls.source.closed.Obj)).rawArrow
      (RelativeClosedPredicateLogic.truthRaw
        (C := RelativeClosedGeneratedQuantifierControls.source.closed.Obj))
def originalTruth := RelativeClosedGeneratedQuantifierControls.retainedLogical.rawArrow RelativeClosedPredicateLogic.truthRaw

theorem original_laws : (RelativeClosedGeneratedQuantifier.SourceOperations.operations RelativeClosedGeneratedQuantifierControls.language originalTruth).Laws :=
  RelativeClosedGeneratedQuantifier.SourceOperations.translated_laws logicalLanguage logicalTruth lawfulMap
    RelativeClosedPredicateLogic.SourceOperations.laws

def initial : RelativeClosedGeneratedQuantifier.Iteration.Stage RelativeClosedGeneratedQuantifierControls.source.closed.Obj where
  symbols := _
  presentation := RelativeClosedGeneratedQuantifierControls.original
  formed := RelativeClosedStructuralImagePresentation.headers RelativeClosedGeneratedQuantifierControls.source RelativeClosedGeneratedQuantifierControls.selection RelativeClosedGeneratedQuantifierControls.constructors
  language := RelativeClosedGeneratedQuantifierControls.language
  truth := originalTruth
  laws := original_laws

theorem truth_read : RawInterpretation.Reads RelativeClosedGeneratedQuantifierControls.meanings originalTruth (operations doctrine).truth :=
  (RelativeClosedGeneratedQuantifierControls.retainedLogical.evaluateArrow_precompose RelativeClosedGeneratedQuantifierControls.meanings RelativeClosedPredicateLogic.truthRaw.code).trans rfl

def model : RelativeClosedGeneratedQuantifier.Iteration.NativeModel doctrine initial where
  meanings := RelativeClosedGeneratedQuantifierControls.meanings
  admitted := RelativeClosedGeneratedQuantifierControls.old
  proposition := RelativeClosedGeneratedQuantifierControls.proposition_read
  conjunction := RelativeClosedGeneratedQuantifierControls.conjunction_read
  truth := truth_read

def firstRoute : RelativeClosedGeneratedQuantifier.Route initial.next.presentation :=
  initial.quantifierRoute .existential RelativeClosedGeneratedQuantifierControls.structuralRoute

def firstImage : power doctrine RelativeClosedGeneratedQuantifierControls.inputSpace ⟶ power doctrine RelativeClosedGeneratedQuantifierControls.outputSpace :=
  RelativeClosedGeneratedQuantifier.NativeMeaning.imageForRead initial.presentation initial.language model.meanings model.admitted doctrine
    model.proposition model.conjunction .existential RelativeClosedGeneratedQuantifierControls.structuralRoute RelativeClosedGeneratedQuantifierControls.originalImage RelativeClosedGeneratedQuantifierControls.structural_route_read

theorem first_image_complete : firstImage = existsOperation doctrine RelativeClosedGeneratedQuantifierControls.originalImage :=
  RelativeClosedGeneratedQuantifier.NativeMeaning.imageForRead_complete initial.presentation initial.language model.meanings model.admitted doctrine
    model.proposition model.conjunction .existential RelativeClosedGeneratedQuantifierControls.structuralRoute RelativeClosedGeneratedQuantifierControls.originalImage RelativeClosedGeneratedQuantifierControls.structural_route_read

theorem first_route_read : RawInterpretation.Reads model.next.meanings firstRoute.arrow firstImage :=
  (model.new_operator_readout .existential RelativeClosedGeneratedQuantifierControls.structuralRoute RelativeClosedGeneratedQuantifierControls.originalImage RelativeClosedGeneratedQuantifierControls.structural_route_read).trans
    (congrArg (fun arrow : power doctrine RelativeClosedGeneratedQuantifierControls.inputSpace ⟶ power doctrine RelativeClosedGeneratedQuantifierControls.outputSpace =>
      some (⟨power doctrine RelativeClosedGeneratedQuantifierControls.inputSpace, power doctrine RelativeClosedGeneratedQuantifierControls.outputSpace, arrow⟩ :
        RelativeClosedSyntax.Interpretation.ArrowValue Type)) first_image_complete.symm)

def secondRoute : RelativeClosedGeneratedQuantifier.Route initial.next.next.presentation :=
  initial.next.quantifierRoute .existential firstRoute

def secondImage : power doctrine (power doctrine RelativeClosedGeneratedQuantifierControls.inputSpace) ⟶ power doctrine (power doctrine RelativeClosedGeneratedQuantifierControls.outputSpace) :=
  RelativeClosedGeneratedQuantifier.NativeMeaning.imageForRead initial.next.presentation initial.next.language model.next.meanings model.next.admitted doctrine
    model.next.proposition model.next.conjunction .existential firstRoute firstImage first_route_read

theorem second_image_complete : secondImage = existsOperation doctrine firstImage :=
  RelativeClosedGeneratedQuantifier.NativeMeaning.imageForRead_complete initial.next.presentation initial.next.language model.next.meanings model.next.admitted doctrine
    model.next.proposition model.next.conjunction .existential firstRoute firstImage first_route_read

theorem the_second_route_quantifies_a_first_stage_added_name :
    firstRoute.arrow.code = .name (Sum.inr ⟨.existential, RelativeClosedGeneratedQuantifierControls.structuralRoute⟩) := rfl

theorem the_second_stage_has_a_complete_independent_operator_reading :
    model.next.next.meanings.evaluateArrow secondRoute.arrow.code =
      some (⟨power doctrine (power doctrine RelativeClosedGeneratedQuantifierControls.inputSpace),
        power doctrine (power doctrine RelativeClosedGeneratedQuantifierControls.outputSpace), existsOperation doctrine firstImage⟩ :
          RelativeClosedSyntax.Interpretation.ArrowValue Type) :=
  model.next.new_operator_readout .existential firstRoute firstImage first_route_read

theorem no_depth_introduces_a_new_proposition_object (depth : Nat) :
    (RelativeClosedGeneratedQuantifier.Iteration.stages initial depth).language.proposition =
      (RelativeClosedGeneratedQuantifier.Iteration.initialInclusion initial depth).object initial.language.proposition :=
  RelativeClosedGeneratedQuantifier.Iteration.proposition_retained initial depth

theorem the_whole_first_stage_functor_is_recovered :
    initial.next.inclusion.functor ⋙ model.next.next.diagram = model.next.diagram :=
  model.next.whole_restriction

def chosen (first second : Nat → Nat) : Nat ⟶ power doctrine RelativeClosedGeneratedQuantifierControls.inputSpace :=
  RelativeClosedGeneratedQuantifierControls.completeInputName first second

def selected (first second : Nat → Nat) : Subobject (power doctrine RelativeClosedGeneratedQuantifierControls.inputSpace ⊗ Nat) :=
  fromSet {whole | whole.1 = chosen first second whole.2}

def selectedName (first second : Nat → Nat) : Nat ⟶ power doctrine (power doctrine RelativeClosedGeneratedQuantifierControls.inputSpace) :=
  name doctrine (selected first second)

def output (first second : Nat → Nat) : Subobject (power doctrine RelativeClosedGeneratedQuantifierControls.outputSpace ⊗ Nat) :=
  family doctrine (selectedName first second ≫ secondImage)

theorem complete_output_read (first second : Nat → Nat)
    (result : power doctrine RelativeClosedGeneratedQuantifierControls.outputSpace) (parameter : Nat) :
    Contains (output first second) (result, parameter) ↔
      result = firstImage (chosen first second parameter) := by
  have complete := (congrArg (fun operation => family doctrine (selectedName first second ≫ operation))
    second_image_complete).trans
    ((exists_supplied doctrine firstImage (selectedName first second)).trans
      (congrArg (doctrine.existsAlong (firstImage ▷ Nat)) (family_name doctrine (selected first second))))
  rw [output, complete, contains_exists]
  constructor
  · rintro ⟨⟨candidate, oldParameter⟩, admitted, reaches⟩
    change (firstImage candidate, oldParameter) = (result, parameter) at reaches
    obtain ⟨answer, unchanged⟩ := Prod.mk.inj reaches
    subst oldParameter
    have suppliedRead := (contains_fromSet
      {whole : power doctrine RelativeClosedGeneratedQuantifierControls.inputSpace ⊗ Nat | whole.1 = chosen first second whole.2}
      (candidate, parameter)).mp admitted
    exact answer.symm.trans (congrArg firstImage suppliedRead)
  · intro read
    refine ⟨(chosen first second parameter, parameter), (contains_fromSet _ _).mpr rfl, ?_⟩
    change (firstImage (chosen first second parameter), parameter) = (result, parameter)
    exact congrArg (fun value => (value, parameter)) read.symm

theorem actual_second_stage_admits_the_complete_first_stage_result (first second : Nat → Nat) (parameter : Nat) :
    Contains (output first second) (firstImage (chosen first second parameter), parameter) :=
  (complete_output_read first second _ parameter).mpr rfl

def future : Nat ⟶ Nat := TypeCat.ofHom Nat.succ

theorem future_retains_the_whole_first_stage_input (first second : Nat → Nat)
    (result : power doctrine RelativeClosedGeneratedQuantifierControls.outputSpace) (parameter : Nat) :
    Contains (family doctrine ((future ≫ selectedName first second) ≫ secondImage)) (result, parameter) ↔
      result = firstImage (chosen first second (parameter + 1)) := by
  have complete := (congrArg (family doctrine) (Category.assoc future (selectedName first second) secondImage)).trans
    (family_substitution doctrine future (selectedName first second ≫ secondImage))
  rw [complete, contains_reindex]
  exact complete_output_read first second result (parameter + 1)

def emptyInput : Subobject (power doctrine RelativeClosedGeneratedQuantifierControls.inputSpace ⊗ Nat) := fromSet ∅
def emptyName : Nat ⟶ power doctrine (power doctrine RelativeClosedGeneratedQuantifierControls.inputSpace) := name doctrine emptyInput

theorem the_actual_second_stage_quantifier_rejects_every_empty_input
    (result : power doctrine RelativeClosedGeneratedQuantifierControls.outputSpace) (parameter : Nat) :
    ¬Contains (family doctrine (emptyName ≫ secondImage)) (result, parameter) := by
  intro held
  have complete := (congrArg (fun operation => family doctrine (emptyName ≫ operation)) second_image_complete).trans
    ((exists_supplied doctrine firstImage emptyName).trans
      (congrArg (doctrine.existsAlong (firstImage ▷ Nat)) (family_name doctrine emptyInput)))
  have admitted := (congrArg (fun predicate : Subobject (power doctrine RelativeClosedGeneratedQuantifierControls.outputSpace ⊗ Nat) =>
    Contains predicate (result, parameter)) complete).mp held
  obtain ⟨candidate, impossible, _⟩ := (contains_exists _ _ _).mp admitted
  exact (contains_fromSet ∅ candidate).mp impossible

end Mettapedia.GSLT.Core.RelativeClosedGeneratedQuantifierIterationControls
