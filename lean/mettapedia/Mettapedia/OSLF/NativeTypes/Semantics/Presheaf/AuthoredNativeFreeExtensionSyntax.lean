import Mettapedia.GSLT.Core.RelativeClosedBareLogicalReadout
import Mettapedia.GSLT.Core.RelativeClosedNamedQuantifiedLogicalReadout
import Mettapedia.CategoryTheory.RelativeClosedPositionedModalInterpretation

/-!
# The shared logical fragment in the actual relative free extension

The translation retains independently formed raw diagrams and maps them
through the named presentation into the existing free object. Its reading
uses the adjunction's extension and its compatible original-diagram
comparison. The independent structural evaluator supplies the other side
of each meaning comparison.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.AuthoredNativeFreeExtensionSyntax

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory Mettapedia.GSLT.Core
open RelativeClosedSyntax GeneratedCategory

universe k
variable (source : ProgramReductionTheoryIsoClasses.{k})

def logicalInclusion := RelativeClosedPredicateLogic.equationInclusion.compose
  (RelativeClosedNamedQuantifiedPresentation.logicalInclusion source.original
    (RelativeClosedBareLogical.selections source) (RelativeClosedBareLogical.constructors source))

def sharedFunctor : Object (RelativeClosedPredicateLogic.signature (C := source.original.closed.Obj)) ⥤
    (RelativeClosedBareLogical.freeObject source).quantified.programTheory.closed.Obj :=
  (logicalInclusion source).functor ⋙
    (RelativeClosedNamedQuantifiedPresentation.unitMap source.original
      (RelativeClosedBareLogical.selections source) (RelativeClosedBareLogical.constructors source)).functor

def sharedArrow {before after : Object (RelativeClosedPredicateLogic.signature
    (C := source.original.closed.Obj))} (raw : RawHom before after) :=
  (sharedFunctor source).map (classOf raw)

theorem shared_identity (object : Object (RelativeClosedPredicateLogic.signature
    (C := source.original.closed.Obj))) :
    sharedArrow source (RawHom.identity object) = 𝟙 ((sharedFunctor source).obj object) :=
  (sharedFunctor source).map_id object

theorem shared_composition {first middle last : Object (RelativeClosedPredicateLogic.signature
    (C := source.original.closed.Obj))} (before : RawHom first middle) (after : RawHom middle last) :
    sharedArrow source (before.compose after) = sharedArrow source before ≫ sharedArrow source after :=
  (sharedFunctor source).map_comp (classOf before) (classOf after)

variable (target : QuantifiedImplicativeProgramTheory.{k})
variable (original : ProgramReductionTheory.Map source.original target.quantified.programTheory)

def independentMeaning := RelativeClosedNamedQuantifiedMeaning.meaning source.original
  target.quantified original.closed.functor target.implication

def independentAssignment := RelativeClosedPredicateLogic.Interpretation.assignment
  original.closed.functor (independentMeaning source target original)

def reading {before after : Object (RelativeClosedPredicateLogic.signature
    (C := source.original.closed.Obj))} (raw : RawHom before after) :=
  RelativeClosedBareLogical.Readout.arrowReading source target original
    (classOf ((logicalInclusion source).rawArrow raw))

theorem independent_arrow_read (code : ArrowCode source.original.closed.Obj
    (RelativeClosedPredicateLogic.symbols source.original.closed.Obj)) :
    (RelativeClosedBareLogical.Readout.model source target original).nativeModel.meanings.evaluateArrow
      (code.map (logicalInclusion source).base (logicalInclusion source).objects
        (logicalInclusion source).arrows) =
      (independentAssignment source target original).evaluateArrow code :=
  (logicalInclusion source).evaluateArrow_precompose
    (RelativeClosedBareLogical.Readout.model source target original).nativeModel.meanings code

theorem independent_object_read (code : ObjectCode source.original.closed.Obj
    (RelativeClosedPredicateLogic.symbols source.original.closed.Obj)) :
    (RelativeClosedBareLogical.Readout.model source target original).nativeModel.meanings.evaluateObject
      (code.map (logicalInclusion source).base (logicalInclusion source).objects
        (logicalInclusion source).arrows) =
      (independentAssignment source target original).evaluateObject code :=
  (logicalInclusion source).evaluateObject_precompose
    (RelativeClosedBareLogical.Readout.model source target original).nativeModel.meanings code

theorem reading_complete {before after : Object (RelativeClosedPredicateLogic.signature
    (C := source.original.closed.Obj))} (raw : RawHom before after)
    {first last : target.quantified.programTheory.closed.Obj} (arrow : first ⟶ last)
    (read : RawInterpretation.Reads (independentAssignment source target original) raw arrow) :
    HEq (reading source target original raw) arrow := by
  have computed := (independent_arrow_read source target original raw.code).trans read
  exact (heq_of_eq (RelativeClosedBareLogical.Readout.complete_arrow_reading source target original _)).trans
    (RelativeClosedSyntax.Interpretation.functor_map_heq
      (RelativeClosedBareLogical.Readout.model source target original).nativeModel.meanings
      (RelativeClosedBareLogical.Readout.model source target original).nativeModel.realization
      ((logicalInclusion source).rawArrow raw) arrow computed)

def objectReading (object : Object (RelativeClosedPredicateLogic.signature
    (C := source.original.closed.Obj))) :=
  (RelativeClosedBareLogical.Readout.model source target original).nativeDiagram.obj
    ((logicalInclusion source).object object)

theorem objectReading_complete (object : Object (RelativeClosedPredicateLogic.signature
    (C := source.original.closed.Obj))) (value : target.quantified.programTheory.closed.Obj)
    (read : RawInterpretation.ObjectReads (independentAssignment source target original) object value) :
    objectReading source target original object = value :=
  RelativeClosedSyntax.Interpretation.objectValue_unique
    (RelativeClosedBareLogical.Readout.model source target original).nativeModel.meanings
    (RelativeClosedBareLogical.Readout.model source target original).nativeModel.realization
    ((logicalInclusion source).object object) value
    ((independent_object_read source target original object.code).trans read)

def readingAt {before after : Object (RelativeClosedPredicateLogic.signature
    (C := source.original.closed.Obj))} (raw : RawHom before after)
    {first last : target.quantified.programTheory.closed.Obj}
    (firstRead : RawInterpretation.ObjectReads (independentAssignment source target original) before first)
    (lastRead : RawInterpretation.ObjectReads (independentAssignment source target original) after last) :
    first ⟶ last :=
  eqToHom (objectReading_complete source target original before first firstRead).symm ≫
    reading source target original raw ≫
      eqToHom (objectReading_complete source target original after last lastRead)

private theorem retype_complete {C : Type k} [Category.{k} C] {X Y X' Y' : C}
    (first : X = X') (last : Y = Y') (before : X ⟶ Y) (after : X' ⟶ Y')
    (same : HEq before after) : eqToHom first.symm ≫ before ≫ eqToHom last = after := by
  cases first
  cases last
  cases same
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

theorem readingAt_complete {before after : Object (RelativeClosedPredicateLogic.signature
    (C := source.original.closed.Obj))} (raw : RawHom before after)
    {first last : target.quantified.programTheory.closed.Obj}
    (firstRead : RawInterpretation.ObjectReads (independentAssignment source target original) before first)
    (lastRead : RawInterpretation.ObjectReads (independentAssignment source target original) after last)
    (arrow : first ⟶ last)
    (read : RawInterpretation.Reads (independentAssignment source target original) raw arrow) :
    readingAt source target original raw firstRead lastRead = arrow :=
  retype_complete
    (objectReading_complete source target original before first firstRead)
    (objectReading_complete source target original after last lastRead)
    (reading source target original raw) arrow (reading_complete source target original raw arrow read)

theorem reading_composition {first middle last : Object (RelativeClosedPredicateLogic.signature
    (C := source.original.closed.Obj))} (before : RawHom first middle) (after : RawHom middle last) :
    reading source target original (before.compose after) =
      reading source target original before ≫ reading source target original after := by
  simp only [reading, RelativeClosedBareLogical.Readout.complete_arrow_reading]
  simpa only [Functor.comp_map, ← classOf_compose, SignatureMap.functor_classOf] using
    ((logicalInclusion source).functor ⋙
      (RelativeClosedBareLogical.Readout.model source target original).nativeDiagram).map_comp
        (classOf before) (classOf after)

theorem universal_read {before after : source.original.closed.Obj} (route : before ⟶ after) :
    HEq (reading source target original (RelativeClosedPredicateLogic.universalRaw route))
      (target.quantified.operations.universal (original.closed.functor.map route)).operation :=
  reading_complete source target original _ _ rfl

theorem existential_read {before after : source.original.closed.Obj} (route : before ⟶ after) :
    HEq (reading source target original (RelativeClosedPredicateLogic.existentialRaw route))
      (target.quantified.operations.existential (original.closed.functor.map route)).operation :=
  reading_complete source target original _ _ rfl

theorem precomposition_read {before after : source.original.closed.Obj} (route : before ⟶ after) :
    HEq (reading source target original (RelativeClosedPredicateLogic.precompositionRaw route))
      (InternalPredicateQuantifier.precomposition target.quantified.operations.predicates
        (original.closed.functor.map route)) :=
  reading_complete source target original _ _
    (RelativeClosedPredicateLogic.Interpretation.precomposition_read original.closed.functor
      (independentMeaning source target original) route)

theorem truth_read :
    HEq (reading source target original (RelativeClosedPredicateLogic.truthRaw
      (C := source.original.closed.Obj))) target.quantified.operations.predicates.truth :=
  reading_complete source target original _ _ rfl

theorem conjunction_read :
    HEq (reading source target original (RelativeClosedPredicateLogic.conjunctionRaw
      (C := source.original.closed.Obj))) target.quantified.operations.predicates.conjunction :=
  reading_complete source target original _ _ rfl

theorem implication_read :
    HEq (reading source target original (RelativeClosedPredicateLogic.implicationRaw
      (C := source.original.closed.Obj))) target.implication.operation :=
  reading_complete source target original _ _ rfl

def spanRaw {events input output : source.original.closed.Obj}
    (observe : events ⟶ input) (project : events ⟶ output) :
    RawHom (RelativeClosedPredicateLogic.power output) (RelativeClosedPredicateLogic.power input) :=
  (RelativeClosedPredicateLogic.precompositionRaw project).compose
    (RelativeClosedPredicateLogic.existentialRaw observe)

theorem span_read {events input output : source.original.closed.Obj}
    (observe : events ⟶ input) (project : events ⟶ output) :
    HEq (reading source target original (spanRaw source observe project))
      (InternalPredicateQuantifier.precomposition target.quantified.operations.predicates
        (original.closed.functor.map project) ≫
          (target.quantified.operations.existential (original.closed.functor.map observe)).operation) :=
  reading_complete source target original _ _ (RawInterpretation.compose _
    (RelativeClosedPredicateLogic.Interpretation.precomposition_read original.closed.functor
      (independentMeaning source target original) project) rfl)

end Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.AuthoredNativeFreeExtensionSyntax
