import Mettapedia.Computability.PNP.CruxLedger

/-!
# PNP residual-side-information subrepair ledger

Static subrepair taxonomy and covered-subrepair list for this branch of
the PNP crux ledger.  The theorem-backed coverage proofs live in the
corresponding semantic coverage modules.
-/

namespace Mettapedia.Computability.PNP

/-- Narrow residual-side-information subrepair classes covered by the current
functional collision packet.  These do not close arbitrary residual side
information; they block the common repair move that treats varying residual data
as if it were source-only data. -/
inductive PNPResidualSideInformationSubrepairClass where
  /-- Same-source/different-residual pairs cannot be decoded from the source
  summary alone. -/
  | sourceDecoderCollisionBlock
  /-- Same-source/different-residual pairs block source-only equality
  predicates for the residual value. -/
  | sourcePredicateCollisionBlock
  /-- Same-source/different-Boolean-target pairs block source-only Boolean
  classifiers. -/
  | sourceBooleanClassifierCollisionBlock
  /-- A concrete two-point same-source residual collision witnesses the
  obstruction. -/
  | concreteSameSourceResidualCollision
  /-- Source-determined residual side information over an invariant base is
  itself unresolved under the involution. -/
  | sourceDeterminedInvariantResidualUnresolved
  /-- Source-determined residual side information over an invariant base has
  zero orbit-resolving mass. -/
  | sourceDeterminedInvariantResidualZeroResolvedMass
  /-- Source-determined residual side information over an invariant base cannot
  give positive doubled advantage. -/
  | sourceDeterminedInvariantResidualNoAdvantage
  /-- Positive doubled advantage over an invariant base forces strictly
  positive orbit-resolving mass for the residual side information. -/
  | positiveAdvantageForcesPositiveResolvedMass
  /-- Strict half-accuracy advantage over an invariant base forces strictly
  positive orbit-resolving mass for the residual side information. -/
  | strictHalfAdvantageForcesPositiveResolvedMass
  /-- Positive orbit-resolving mass over an invariant base already forces the
  pure residual obstruction package: non-source-determined residual data,
  supported same-base residual variation, and a supported non-source-only
  residual equality test. -/
  | positiveResolvedMassPureResidualPackage
  /-- The manuscript's exact post-switch active orbit already realizes
  positive resolved mass together with the pure residual obstruction package
  on the concrete visible surface. -/
  | exactPostSwitchConcretePureResidualWitness
  /-- The manuscript's exact post-switch active-orbit prediction witness is
  already a fork-obstruction witness on the same concrete surface. -/
  | exactPostSwitchPredictionWitnessForcesForkObstruction
  /-- Positive doubled advantage over an invariant base forces the residual side
  information to be non-source-determined. -/
  | positiveAdvantageForcesNonSourceDeterminedResidual
  /-- Strict half-accuracy advantage over an invariant base forces the residual
  side information to be non-source-determined. -/
  | strictHalfAdvantageForcesNonSourceDeterminedResidual
  /-- Positive doubled advantage over an invariant base exposes a positive
  support residual collision over the base. -/
  | positiveAdvantageSupportedResidualCollision
  /-- Positive doubled advantage over an invariant base exposes a supported
  residual value whose equality test is not source-only. -/
  | positiveAdvantageSupportedSourcePredicateBlock
  /-- If every supported residual equality test is source-only, positive
  doubled advantage over an invariant base is impossible. -/
  | supportedSourcePredicatesNoPositiveAdvantage
  /-- If the classifier is already source-only on positive support, syntactic
  mention of the residual side data cannot create positive doubled advantage. -/
  | supportwiseSourceClassifierNoPositiveAdvantage
  /-- Strict half-accuracy advantage over an invariant base exposes a positive
  support residual collision over the base. -/
  | strictHalfAdvantageSupportedResidualCollision
  /-- Strict half-accuracy advantage over an invariant base exposes a supported
  residual value whose equality test is not source-only. -/
  | strictHalfAdvantageSupportedSourcePredicateBlock
  /-- If every supported residual equality test is source-only, strict
  half-accuracy advantage over an invariant base is impossible. -/
  | supportedSourcePredicatesNoStrictHalfAdvantage
  /-- If the classifier is already source-only on positive support, syntactic
  mention of the residual side data cannot beat half accuracy. -/
  | supportwiseSourceClassifierNoStrictHalfAdvantage
  /-- Positive doubled advantage over an invariant base must separate some
  positive-support involution pair at the final classifier output. -/
  | positiveAdvantagePredictionSeparation
  /-- Strict half-accuracy advantage over an invariant base must separate some
  positive-support involution pair at the final classifier output. -/
  | strictHalfAdvantagePredictionSeparation
  deriving DecidableEq, Repr

/-- The exact narrow residual-side-information subrepairs covered by the
current functional collision and resolution-cost packets. -/
def currentPNPResidualSideInformationCoveredSubrepairs :
    List PNPResidualSideInformationSubrepairClass :=
  [.sourceDecoderCollisionBlock,
    .sourcePredicateCollisionBlock,
    .sourceBooleanClassifierCollisionBlock,
    .concreteSameSourceResidualCollision,
    .sourceDeterminedInvariantResidualUnresolved,
    .sourceDeterminedInvariantResidualZeroResolvedMass,
    .sourceDeterminedInvariantResidualNoAdvantage,
    .positiveAdvantageForcesPositiveResolvedMass,
    .strictHalfAdvantageForcesPositiveResolvedMass,
    .positiveResolvedMassPureResidualPackage,
    .exactPostSwitchConcretePureResidualWitness,
    .exactPostSwitchPredictionWitnessForcesForkObstruction,
    .positiveAdvantageForcesNonSourceDeterminedResidual,
    .strictHalfAdvantageForcesNonSourceDeterminedResidual,
    .positiveAdvantageSupportedResidualCollision,
    .positiveAdvantageSupportedSourcePredicateBlock,
    .supportedSourcePredicatesNoPositiveAdvantage,
    .supportwiseSourceClassifierNoPositiveAdvantage,
    .strictHalfAdvantageSupportedResidualCollision,
    .strictHalfAdvantageSupportedSourcePredicateBlock,
    .supportedSourcePredicatesNoStrictHalfAdvantage,
    .supportwiseSourceClassifierNoStrictHalfAdvantage,
    .positiveAdvantagePredictionSeparation,
    .strictHalfAdvantagePredictionSeparation]

/-- The narrow residual-side-information subrepair coverage list is exact. -/
theorem currentPNPResidualSideInformationCoveredSubrepairs_exact
    (repair : PNPResidualSideInformationSubrepairClass) :
    repair ∈ currentPNPResidualSideInformationCoveredSubrepairs := by
  cases repair <;> simp [currentPNPResidualSideInformationCoveredSubrepairs]

end Mettapedia.Computability.PNP
