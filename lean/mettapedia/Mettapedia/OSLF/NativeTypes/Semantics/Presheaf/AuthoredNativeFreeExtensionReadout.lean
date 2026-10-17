import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.AuthoredProgramReduction
import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.AuthoredNativeFreeExtensionSyntax
import Mettapedia.CategoryTheory.AsSmallPredicateDoctrine
import Mettapedia.CategoryTheory.HigherOrderInternalPredicateQuantifiedObject
import Mettapedia.CategoryTheory.InternalPredicateModalSpanComparison
import Mettapedia.GSLT.Topos.PresheafPredicateHigherOrder
import Mettapedia.OSLF.NativeTypes.Generation.CurriedNativeStructuralMeaning
import Mettapedia.OSLF.NativeTypes.Generation.CurriedNativeModalResponse

/-!
# Presheaf reading of the authored relative free extension

The actual carrier and receipt-image source receives the existing bare
logical free extension. The target operations are earned by the original
binding presheaf doctrine and its category equivalence. Constructor and
event-span diagrams retain every contextual argument and receipt. Their
free-extension interpretation is compared with the independently built
presheaf predicate operations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.AuthoredNativeFreeExtensionReadout

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open Mettapedia.CategoryTheory Mettapedia.GSLT.Core
open Mettapedia.OSLF.NativeTypes.Generation
open Mettapedia.TypeTheory Mettapedia.TypeTheory.Calculi.NativeDependent
open NativeLocalTypeFormers ContextualLocalUniverses DisplayedPresheafComprehension
open CurriedBindingLanguage
open RelativeClosedSyntax GeneratedCategory

variable (installed : AuthoredPipeline.Installed)

abbrev doctrine := AsSmallPredicateDoctrine.higherOrder
  (Mettapedia.GSLT.Topos.PresheafPredicateHigherOrder.higherOrder
    (Worlds (AuthoredProgramReduction.language installed)))

def target : QuantifiedImplicativeProgramTheory.{1} where
  quantified := {
    programTheory := AuthoredProgramReduction.sourceTheory installed
    operations := HigherOrderInternalPredicateQuantifiedObject.operations (doctrine installed) }
  implication := HigherOrderInternalPredicateImplication.qualification (doctrine installed)

def original : ProgramReductionTheory.Map (AuthoredProgramReduction.sourceTheory installed)
    (target installed).quantified.programTheory :=
  ProgramReductionTheory.Map.identity (AuthoredProgramReduction.sourceTheory installed)

def freeTheory := RelativeClosedBareLogical.freeObject (AuthoredProgramReduction.sourceClass installed)

def interpretation := RelativeClosedBareLogical.extension
  (AuthoredProgramReduction.sourceClass installed) (target installed) (original installed)

def oldComparison := RelativeClosedBareLogical.extensionRestriction
  (AuthoredProgramReduction.sourceClass installed) (target installed) (original installed)

def constructorSyntax (constructor : installed.operational.declarations.Constructor) :=
  RelativeClosedNamedQuantifiedPresentation.constructorArrow
    (AuthoredProgramReduction.sourceTheory installed)
    (RelativeClosedBareLogical.selections (AuthoredProgramReduction.sourceClass installed))
    (RelativeClosedBareLogical.constructors (AuthoredProgramReduction.sourceClass installed))
    (AuthoredProgramReduction.constructorOrigin installed constructor)

theorem constructor_named_read (constructor : installed.operational.declarations.Constructor) :
    HEq (RelativeClosedBareLogical.Readout.arrowReading
      (AuthoredProgramReduction.sourceClass installed) (target installed) (original installed)
      (classOf ((RelativeClosedStructuralImagePresentation.nativeInclusion
        (AuthoredProgramReduction.sourceTheory installed)
        (RelativeClosedBareLogical.selections (AuthoredProgramReduction.sourceClass installed))
        (RelativeClosedBareLogical.constructors (AuthoredProgramReduction.sourceClass installed))).rawArrow
          (RelativeClosedStructuralImagePresentation.namedRaw
            (AuthoredProgramReduction.sourceTheory installed)
            (RelativeClosedBareLogical.selections (AuthoredProgramReduction.sourceClass installed))
            (RelativeClosedBareLogical.constructors (AuthoredProgramReduction.sourceClass installed))
            (AuthoredProgramReduction.constructorOrigin installed constructor)))))
      (HigherOrderInternalPredicateQuantifier.existsOperation (doctrine installed)
        (AuthoredProgramReduction.constructorOrigin installed constructor).term) :=
  RelativeClosedBareLogical.Readout.entire_constructor_function
    (AuthoredProgramReduction.sourceClass installed) (target installed) (original installed)
    (AuthoredProgramReduction.constructorOrigin installed constructor)

def existentialReading {before after : AuthoredProgramReduction.Category installed}
    (route : before ⟶ after) :
    HigherOrderInternalPredicateQuantifier.power (doctrine installed) before ⟶
      HigherOrderInternalPredicateQuantifier.power (doctrine installed) after :=
  AuthoredNativeFreeExtensionSyntax.readingAt
    (AuthoredProgramReduction.sourceClass installed) (target installed) (original installed)
    (RelativeClosedPredicateLogic.existentialRaw route)
    (RelativeClosedPredicateLogic.Interpretation.power_read _ _ before)
    (RelativeClosedPredicateLogic.Interpretation.power_read _ _ after)

theorem existentialReading_complete {before after : AuthoredProgramReduction.Category installed}
    (route : before ⟶ after) :
    existentialReading installed route =
      HigherOrderInternalPredicateQuantifier.existsOperation (doctrine installed) route :=
  AuthoredNativeFreeExtensionSyntax.readingAt_complete
    (AuthoredProgramReduction.sourceClass installed) (target installed) (original installed)
    (RelativeClosedPredicateLogic.existentialRaw route) _ _ _ rfl

def spanSyntax {events input output : AuthoredProgramReduction.Category installed}
    (observe : events ⟶ input) (project : events ⟶ output) :=
  AuthoredNativeFreeExtensionSyntax.sharedArrow
    (AuthoredProgramReduction.sourceClass installed)
    (AuthoredNativeFreeExtensionSyntax.spanRaw (AuthoredProgramReduction.sourceClass installed)
      observe project)

def spanReading {events input output : AuthoredProgramReduction.Category installed}
    (observe : events ⟶ input) (project : events ⟶ output) :
    HigherOrderInternalPredicateQuantifier.power (doctrine installed) output ⟶
      HigherOrderInternalPredicateQuantifier.power (doctrine installed) input :=
  AuthoredNativeFreeExtensionSyntax.readingAt
    (AuthoredProgramReduction.sourceClass installed) (target installed) (original installed)
    (AuthoredNativeFreeExtensionSyntax.spanRaw (AuthoredProgramReduction.sourceClass installed)
      observe project)
    (RelativeClosedPredicateLogic.Interpretation.power_read _ _ output)
    (RelativeClosedPredicateLogic.Interpretation.power_read _ _ input)

theorem spanReading_complete {events input output : AuthoredProgramReduction.Category installed}
    (observe : events ⟶ input) (project : events ⟶ output) :
    spanReading installed observe project =
      InternalPredicateModalSpanComparison.operation (doctrine installed)
        (⟨events, observe, project⟩ : InternalPredicateModalSpanComparison.Span _ input output) :=
  AuthoredNativeFreeExtensionSyntax.readingAt_complete
    (AuthoredProgramReduction.sourceClass installed) (target installed) (original installed)
    (AuthoredNativeFreeExtensionSyntax.spanRaw (AuthoredProgramReduction.sourceClass installed)
      observe project) _ _ _ (RawInterpretation.compose _
        (RelativeClosedPredicateLogic.Interpretation.precomposition_read _ _ project) rfl)

theorem constructor_supplied (constructor : installed.operational.declarations.Constructor)
    {parameter : AuthoredProgramReduction.Category installed}
    (predicate : parameter ⟶ HigherOrderInternalPredicateQuantifier.power (doctrine installed)
      (AuthoredProgramReduction.constructorOrigin installed constructor).arguments) :
    HigherOrderInternalPredicateObject.family (doctrine installed)
      (predicate ≫ existentialReading installed
        (AuthoredProgramReduction.constructorOrigin installed constructor).term) =
      (doctrine installed).existsAlong
        ((AuthoredProgramReduction.constructorOrigin installed constructor).term ▷ parameter)
        (HigherOrderInternalPredicateObject.family (doctrine installed) predicate) := by
  rw [existentialReading_complete]
  exact HigherOrderInternalPredicateQuantifier.exists_supplied (doctrine installed) _ predicate

theorem span_supplied {events input output parameter : AuthoredProgramReduction.Category installed}
    (observe : events ⟶ input) (project : events ⟶ output)
    (post : parameter ⟶ HigherOrderInternalPredicateQuantifier.power (doctrine installed) output) :
    HigherOrderInternalPredicateObject.family (doctrine installed)
      (post ≫ spanReading installed observe project) =
      (doctrine installed).existsAlong (observe ▷ parameter)
        ((doctrine installed).reindex (project ▷ parameter)
          (HigherOrderInternalPredicateObject.family (doctrine installed) post)) := by
  rw [spanReading_complete]
  exact InternalPredicateModalSpanComparison.operation_supplied (doctrine installed) _ post

theorem span_parameter_substitution
    {events input output first second : AuthoredProgramReduction.Category installed}
    (observe : events ⟶ input) (project : events ⟶ output) (incoming : first ⟶ second)
    (post : second ⟶ HigherOrderInternalPredicateQuantifier.power (doctrine installed) output) :
    HigherOrderInternalPredicateObject.family (doctrine installed)
      ((incoming ≫ post) ≫ spanReading installed observe project) =
      (doctrine installed).reindex (input ◁ incoming)
        (HigherOrderInternalPredicateObject.family (doctrine installed)
          (post ≫ spanReading installed observe project)) := by
  rw [spanReading_complete]
  exact InternalPredicateModalSpanComparison.operation_future (doctrine installed) _ incoming post

end Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.AuthoredNativeFreeExtensionReadout
