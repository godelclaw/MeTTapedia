import Mettapedia.QuantumTheory.YangMills.ContinuumOSReconstruction
import Mettapedia.QuantumTheory.YangMills.SupportGrowth
import Mettapedia.QuantumTheory.YangMills.WilsonExtractionRecombinationConstant

/-!
# Yang-Mills five-input completion steelman

This module steelmans the five remaining inputs isolated in the Ben-facing
Yang-Mills report.  It separates what is already arithmetic/formal, what is a
manuscript branch choice, what is a named analytic or classical import, and
what remains the central Wilson RG theorem.

Scope:

* The extraction/recombination constant is adjudicated on a concrete finite
  Wilson-block majorant realization.  The proposed Appendix-O ledger has
  conditional bootstrap arithmetic, while the v14 as-written component claims
  have explicit counterexamples.
* The support recurrence dichotomy reuses the checked good/bad recurrences in
  `SupportGrowth`.
* The two-marked correlation identity is recorded as a named API, with a small
  canary showing that a one-marked pushforward identity alone does not imply
  it.
* KP convergence and Wilson reflection positivity are represented as
  Lean-facing classical-import APIs that plug into the existing OS scaffold.
* The actual Wilson Yang-Mills RG recursion is recorded as the first
  load-bearing analytic theorem: it is exactly the bridge from the checked
  arithmetic recursion to the lattice mass-gap/clustering inputs needed by
  OS reconstruction.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills

/-- Verdict tags for each steelmanned input. -/
inductive CompletionSteelmanVerdict where
  | verified
  | reducedToNamedAssumption
  | refutedOrInconsistent
  | blockedByUnreadableArtifact
deriving DecidableEq, Repr

/-! ## 1. Extraction/recombination constant

The source-verified verdict and conditional depth calculation are the headline
theorems `not_v14LiteralExtractionRecombinationClaims` and
`proposedMajorantLedger_leastDepth_and_leastEvenDepth`.  No second wrapper is
introduced here. -/

/-! ## 2. Support recurrence -/

/-- The branch choice the manuscript must make for the glue support recurrence. -/
inductive BenGlueSupportBranch where
  | coarsenThenThicken
  | thickenOnly
  | notSpecified
deriving DecidableEq, Repr

/-- The report location whose prose must choose the safe support recurrence.
This is a repository-relative pointer, suitable for public documentation. -/
def benGlueSupportDecisionPoint : String :=
  "papers/benxiv/goertzel_ym.tex: item 'Which support recurrence the glue satisfies'"

/-- If the glue uses coarsen-then-thicken, the already checked support theorem
gives a uniform `O(1)` collar. -/
theorem benGlueSupport_safeBranch_uniform
    {r : ℕ → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hrec : ∀ j, r (j + 1) ≤ r j / 2 + A) :
    ∀ J, r J ≤ r 0 / 2 ^ J + 2 * A :=
  good_support_recurrence_uniform_bound_two hA hrec

/-- If the glue is only thicken-only with a positive collar, the tight envelope
eventually exceeds every fixed support bound. -/
theorem benGlueSupport_badBranch_unbounded
    {r0 A : ℝ} (hA : 0 < A) (M : ℝ) :
    ∃ J : ℕ, M < badSupportEnvelope r0 A J :=
  badSupportEnvelope_unbounded hA M

/-- Named assumption for the manuscript clarification that picks the safe
support branch. -/
def BenGlueUsesCoarsenThenThicken (branch : BenGlueSupportBranch) : Prop :=
  branch = .coarsenThenThicken

theorem benGlueSupportClarification_suffices_for_safe_branch
    (h : BenGlueUsesCoarsenThenThicken .coarsenThenThicken) :
    BenGlueUsesCoarsenThenThicken .coarsenThenThicken := h

/-! ## 3. Two-marked correlation identity -/

/-- One-marked pushforward data: expectations are transported by `Q`. -/
structure BenOneMarkedPushforwardAPI (Obs0 ObsJ : Type*) where
  Q : Obs0 → ObsJ
  expectation0 : Obs0 → ℝ
  expectationJ : ObsJ → ℝ
  oneMarked : ∀ A, expectation0 A = expectationJ (Q A)

/-- The two-marked centered/truncated correlation identity needed by the
back-propagation step. -/
structure BenTwoMarkedCorrelationIdentityAPI (Obs0 ObsJ : Type*) where
  Q : Obs0 → ObsJ
  tau0 : Obs0 → Obs0
  tauJ : ObsJ → ObsJ
  centeredCorr0 : Obs0 → Obs0 → ℝ
  centeredCorrJ : ObsJ → ObsJ → ℝ
  twoMarked :
    ∀ A B, centeredCorr0 A (tau0 B) =
      centeredCorrJ (Q A) (tauJ (Q B))

def oneMarkedCanaryQ (_ : Unit) : Unit := ()
def oneMarkedCanaryExpectation0 (_ : Unit) : ℝ := 0
def oneMarkedCanaryExpectationJ (_ : Unit) : ℝ := 0
def oneMarkedCanaryTau0 (x : Unit) : Unit := x
def oneMarkedCanaryTauJ (x : Unit) : Unit := x
def oneMarkedCanaryCorr0 (_ _ : Unit) : ℝ := 0
def oneMarkedCanaryCorrJ (_ _ : Unit) : ℝ := 1

theorem oneMarkedCanary_pushforward :
    ∀ A : Unit,
      oneMarkedCanaryExpectation0 A =
        oneMarkedCanaryExpectationJ (oneMarkedCanaryQ A) := by
  intro A
  cases A
  rfl

/-- Canary: a one-marked pushforward identity alone does not imply the
two-marked centered correlation identity. -/
theorem oneMarkedPushforward_does_not_imply_twoMarked_canary :
    ¬ (∀ A B : Unit,
      oneMarkedCanaryCorr0 A (oneMarkedCanaryTau0 B) =
        oneMarkedCanaryCorrJ (oneMarkedCanaryQ A)
          (oneMarkedCanaryTauJ (oneMarkedCanaryQ B))) := by
  intro h
  have hbad := h () ()
  norm_num [oneMarkedCanaryCorr0, oneMarkedCanaryCorrJ] at hbad

/-! ## 4. KP convergence and Wilson reflection positivity -/

/-- Lean-facing API for importing Kotecky-Preiss convergence at the stopping
scale. -/
structure KPStoppingScaleInput where
  polymerNormSmall : Prop
  contourCompatibility : Prop
  sourceSummability : Prop
  largeFieldTailDecays : Prop
  kpConverges :
    polymerNormSmall ∧ contourCompatibility ∧
      sourceSummability ∧ largeFieldTailDecays

/-- Lean-facing API for importing Wilson-measure reflection positivity. -/
structure WilsonReflectionPositivityInput where
  reflectionPositiveFunctional : Prop
  reflectionPositiveCone : Prop
  finiteVolumeCompatible : Prop
  boundaryLimitCompatible : Prop
  reflectionPositive :
    reflectionPositiveFunctional ∧ reflectionPositiveCone

def WilsonReflectionPositivityInput.toOSReflectionPositivityInput
    (rp : WilsonReflectionPositivityInput) :
    OSReflectionPositivityInput where
  reflectionPositiveFunctional := rp.reflectionPositiveFunctional
  reflectionPositiveCone := rp.reflectionPositiveCone
  reflectionPositive := rp.reflectionPositive

/-- Classical constructive imports, packaged so they can be plugged into the
existing OS scaffold without pretending to prove KP or Wilson RP here. -/
structure BenClassicalConstructiveImports where
  kp : KPStoppingScaleInput
  reflectionPositivity : WilsonReflectionPositivityInput

/-- The classical Wilson RP API supplies the exact reflection-positivity input
expected by the current OS scaffold. -/
def wilsonReflectionPositivity_plugs_into_os
    (imports : BenClassicalConstructiveImports) :
    OSReflectionPositivityInput :=
  imports.reflectionPositivity.toOSReflectionPositivityInput

/-! ## 5. Real Wilson RG map recursion -/

/-- Sublemma ledger for the actual Wilson Yang-Mills RG recursion theorem. -/
structure BenWilsonRGRecursionSublemmas where
  oneStepMapDefined : Prop
  extractionRecombination : Prop
  actualWilsonRecursionConstant : ℝ
  actualWilsonRecursionConstant_nonneg : 0 ≤ actualWilsonRecursionConstant
  actualWilsonRecursionConstantBoundProved : Prop
  supportUsesCoarsenThenThicken :
    BenGlueUsesCoarsenThenThicken .coarsenThenThicken
  twoMarkedCorrelationIdentity :
    ∃ Obs0 ObsJ : Type, Nonempty (BenTwoMarkedCorrelationIdentityAPI Obs0 ObsJ)
  irrelevantContraction :
    HasTwoSourceBootstrapSlack actualWilsonRecursionConstant 2 16
  relevantMarginalControl : Prop
  twoSourceBootstrapSources : Prop
  errorSummability : Prop
  kpAtStoppingScale : KPStoppingScaleInput
  wilsonReflectionPositivity : WilsonReflectionPositivityInput

/-- The central analytic theorem still needed from the actual Wilson
Yang-Mills RG map: the checked arithmetic and support/correlation inputs must
produce the lattice mass-gap and clustering packet consumed by OS
reconstruction. -/
structure BenActualWilsonRGMapRecursionTheorem
    (corr : SpatialCorrelation) where
  sublemmas : BenWilsonRGRecursionSublemmas
  lambdaToKirk : BenLambdaToKirkOpenInput corr
  constantMatchesBridge :
    lambdaToKirk.Ctrue = sublemmas.actualWilsonRecursionConstant

/-- If the actual Wilson RG recursion theorem is supplied, together with an OS
machine, the existing conditional endpoint yields the continuum spectral gap. -/
def BenActualWilsonRGMapRecursionTheorem.toContinuumConditional
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {Δ : ℝ} {corr : SpatialCorrelation}
    (rg : BenActualWilsonRGMapRecursionTheorem corr)
    (machine : KirkOSReconstructionMachine A Δ corr) :
    BenYMContinuumOSConditional A Δ corr where
  lambdaBridge := rg.lambdaToKirk
  reflectionPositivity :=
    rg.sublemmas.wilsonReflectionPositivity.toOSReflectionPositivityInput
  reconstructionMachine := machine

theorem actualWilsonRGMapRecursion_then_continuumMassGap
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {Δ : ℝ} {corr : SpatialCorrelation}
    (rg : BenActualWilsonRGMapRecursionTheorem corr)
    (machine : KirkOSReconstructionMachine A Δ corr) :
    HasSpectralMassGap A Δ :=
  (rg.toContinuumConditional machine).continuumMassGap

/-- The first load-bearing missing theorem after the arithmetic, support
dichotomy, two-marked API, and classical import APIs are made explicit. -/
def FirstLoadBearingYangMillsCompletionInput (corr : SpatialCorrelation) : Prop :=
  Nonempty (BenActualWilsonRGMapRecursionTheorem corr)

/-! ## Summary table -/

/-- One row in the five-input steelman table. -/
structure CompletionSteelmanRow where
  item : Nat
  label : String
  verdict : CompletionSteelmanVerdict
  evidence : String
  nextObligation : String
deriving Repr

def recombinationConstantSteelmanRow : CompletionSteelmanRow where
  item := 1
  label := "Extraction/recombination constant"
  verdict := .refutedOrInconsistent
  evidence :=
    "WilsonBlockMajorant proves norm-one coordinate truncation on actual gauge-invariant finite Wilson observables. projectionRangeSpecification_does_not_imply_bound_two refutes transfer from a range-only projection; polymerActivityMajorant_recombineByUnion_le proves union regrouping has norm one; fourteen_lt_contactStrip_rail_contacts refutes the literal total-contact reading of 14."
  nextObligation :=
    "Specify the dimension<=16 invariant basis and dual jets, prove their uniform conditioning, and prove the rooted cumulant-generation/tree-graph bound in the same majorant norm. Then multiply those actual-map factors and rerun the parameterized depth theorem."

def supportRecurrenceSteelmanRow : CompletionSteelmanRow where
  item := 2
  label := "Support recurrence"
  verdict := .reducedToNamedAssumption
  evidence :=
    "benGlueSupport_safeBranch_uniform gives uniform support for coarsen-then-thicken; benGlueSupport_badBranch_unbounded shows thicken-only grows past every bound."
  nextObligation :=
    "Manuscript must assert BenGlueUsesCoarsenThenThicken at the glue-support decision point."

def twoMarkedIdentitySteelmanRow : CompletionSteelmanRow where
  item := 3
  label := "Two-marked correlation identity"
  verdict := .reducedToNamedAssumption
  evidence :=
    "BenTwoMarkedCorrelationIdentityAPI states the needed centered/truncated identity; oneMarkedPushforward_does_not_imply_twoMarked_canary refutes deriving it from one-marked pushforward alone."
  nextObligation :=
    "Prove the two-marked identity or carry it as an explicit named assumption."

def kpWilsonSteelmanRow : CompletionSteelmanRow where
  item := 4
  label := "KP convergence and Wilson reflection positivity"
  verdict := .reducedToNamedAssumption
  evidence :=
    "KPStoppingScaleInput and WilsonReflectionPositivityInput state the classical APIs; wilsonReflectionPositivity_plugs_into_os verifies the RP packet matches the OS scaffold."
  nextObligation :=
    "Instantiate the classical imports with polymer smallness, contour compatibility, source summability, tail decay, reflection functional/cone, and boundary-limit compatibility."

def realRGRecursionSteelmanRow : CompletionSteelmanRow where
  item := 5
  label := "Actual Wilson RG map recursion"
  verdict := .reducedToNamedAssumption
  evidence :=
    "BenActualWilsonRGMapRecursionTheorem is the central theorem; actualWilsonRGMapRecursion_then_continuumMassGap shows it plugs into the existing OS endpoint."
  nextObligation :=
    "Prove FirstLoadBearingYangMillsCompletionInput for the actual Wilson YM RG map."

def proBlueprintSteelmanRow : CompletionSteelmanRow where
  item := 6
  label := "Pro completion blueprint artifact"
  verdict := .verified
  evidence :=
    "The 16-page July 2026 blueprint was read and source-compared. It is theorem-planning guidance from the formalization effort, not manuscript content; its norm-one majorant proposal is realized by WilsonBlockMajorant, while its basis and recombination factors were proposals rather than derived v14 constants."
  nextObligation :=
    "Use the audited dependency map; do not attribute blueprint repairs or constants to the v14 manuscript."

def currentYangMillsCompletionSteelmanRows : List CompletionSteelmanRow :=
  [ recombinationConstantSteelmanRow
  , supportRecurrenceSteelmanRow
  , twoMarkedIdentitySteelmanRow
  , kpWilsonSteelmanRow
  , realRGRecursionSteelmanRow
  , proBlueprintSteelmanRow
  ]

theorem currentYangMillsCompletionSteelmanRows_length :
    currentYangMillsCompletionSteelmanRows.length = 6 := by
  rfl

theorem fivePrimaryCompletionInputs_classified :
    (currentYangMillsCompletionSteelmanRows.take 5).length = 5 := by
  rfl

theorem recombinationConstantSteelman_refutedOrInconsistent :
    recombinationConstantSteelmanRow.verdict = .refutedOrInconsistent := by
  rfl

theorem supportRecurrenceSteelman_reduced :
    supportRecurrenceSteelmanRow.verdict = .reducedToNamedAssumption := by
  rfl

theorem twoMarkedIdentitySteelman_reduced :
    twoMarkedIdentitySteelmanRow.verdict = .reducedToNamedAssumption := by
  rfl

theorem kpWilsonSteelman_reduced :
    kpWilsonSteelmanRow.verdict = .reducedToNamedAssumption := by
  rfl

theorem realRGRecursionSteelman_reduced :
    realRGRecursionSteelmanRow.verdict = .reducedToNamedAssumption := by
  rfl

theorem proBlueprintSteelman_verified :
    proBlueprintSteelmanRow.verdict = .verified := by
  rfl

end YangMills
end QuantumTheory
end Mettapedia
