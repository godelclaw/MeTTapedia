import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveSubjectReduction
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.ProofRelevantStructuralComputation
import Mettapedia.GSLT.Core.Ultrainfinite

/-!
# Formation-sensitive typing of retained structural executions

The execution carrier is the existing GSLT `Route`, and its edges are the
existing native structural receipts. No second transition relation or typing
judgment is introduced. Contextual preservation supplies a typed endpoint for
every receipt and retains the complete path at its original context and type.

These are native pure computation receipts, including declared root evidence
when the root support matches the selected typing rules. Effect-machine
transitions are not thereby admitted into definitional conversion. A guest
checker still needs its actual source-to-native execution correspondence.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace FormationSensitive.Execution

open Declaration ProofRelevantStructuralComputation
open Mettapedia.GSLT.Ultrainfinite (Route)

universe uEvidence
variable {Head : Type} {n : Nat}

/-- A finite native execution retains each selected structural receipt. -/
abbrev Path (computation : ProofRelevantRootComputation.{uEvidence} Head)
    (headEq : Head → Head → Prop) (source target : Tm Head n) :=
  Route (StructuralStepReceipt computation headEq) source target

/-- The display, formed context and chosen receipts are retained together. -/
structure TypedPath (R : Rules Head)
    (computation : ProofRelevantRootComputation.{uEvidence} Head)
    (context : Ctx Head n) (source target type : Tm Head n) where
  sourceJudgment : Judgment R context source type
  path : Path computation R.headEq source target

/-- Qualify the established receipt support against the actual root rules. -/
theorem receipt_preserves {R : Rules Head}
    {computation : ProofRelevantRootComputation.{uEvidence} Head}
    (support : R.computation = computation.support)
    (universes : UniverseRegularity R) (piBoundary : PiConversionBoundary R)
    (sigmaBoundary : SigmaConversionBoundary R) (heads : HeadPreservation R)
    (roots : RootPreservation R)
    {context : Ctx Head n} {source target type : Tm Head n}
    (judgment : Judgment R context source type)
    (receipt : StructuralStepReceipt computation R.headEq source target) :
    Judgment R context target type := by
  apply judgment.step_preserves universes piBoundary sigmaBoundary heads roots
  rw [support]
  exact receipt.toSupport

/-- Replaying any finite receipt path constructs the actual refined typing
judgment at its endpoint; the entire context and displayed type remain fixed. -/
theorem Path.preserves {R : Rules Head}
    {computation : ProofRelevantRootComputation.{uEvidence} Head}
    (support : R.computation = computation.support)
    (universes : UniverseRegularity R) (piBoundary : PiConversionBoundary R)
    (sigmaBoundary : SigmaConversionBoundary R) (heads : HeadPreservation R)
    (roots : RootPreservation R)
    {context : Ctx Head n} {source target type : Tm Head n}
    (path : Path computation R.headEq source target)
    (judgment : Judgment R context source type) : Judgment R context target type := by
  induction path with
  | refl => exact judgment
  | cons receipt rest ih =>
      exact ih (receipt_preserves support universes piBoundary sigmaBoundary heads roots
        judgment receipt)

/-- Typed paths concatenate only at a shared endpoint, context and display.
The selected rule occurrences are retained by the existing path append. -/
def TypedPath.append {R : Rules Head}
    {computation : ProofRelevantRootComputation.{uEvidence} Head}
    {context : Ctx Head n} {first middle last type : Tm Head n}
    (earlier : TypedPath R computation context first middle type)
    (later : TypedPath R computation context middle last type) :
    TypedPath R computation context first last type :=
  ⟨earlier.sourceJudgment, earlier.path.append later.path⟩

theorem TypedPath.append_length {R : Rules Head}
    {computation : ProofRelevantRootComputation.{uEvidence} Head}
    {context : Ctx Head n} {first middle last type : Tm Head n}
    (earlier : TypedPath R computation context first middle type)
    (later : TypedPath R computation context middle last type) :
    (earlier.append later).path.length = earlier.path.length + later.path.length :=
  Route.length_append earlier.path later.path

/-- Retaining typing information does not identify receipt paths that happen
to have the same endpoints. Different retained paths remain distinguishable. -/
theorem TypedPath.distinct_of_paths {R : Rules Head}
    {computation : ProofRelevantRootComputation.{uEvidence} Head}
    {context : Ctx Head n} {source target type : Tm Head n}
    {first second : TypedPath R computation context source target type}
    (different : first.path ≠ second.path) : first ≠ second := by
  intro same
  exact different (congrArg TypedPath.path same)

end FormationSensitive.Execution
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
