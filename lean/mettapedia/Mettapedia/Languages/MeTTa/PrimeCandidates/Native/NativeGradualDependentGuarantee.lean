import Mettapedia.Languages.MeTTa.PrimeCandidates.Native.NativeGradualDependentNaturality
import Mettapedia.Languages.MeTTa.PrimeCandidates.Native.NativeGradualDependentInteraction
import Mettapedia.Languages.MeTTa.PrimeCandidates.Native.NativeProgramGradualGuarantee
import Mettapedia.Languages.MeTTa.PrimeCandidates.Native.NativeParallelGradualGuarantee

/-!
# Native instances of displayed evidence and Need checking

candidate graduality is displayed over unchanged raw semantics.  Precision fills
an exact-evidence fibre or records local blame; it does not add an unknown term
to kernel conversion.  This file closes the generic laws needed to use that
design compositionally:

* every state refines suspension while exact evidence and current blame remain
  rigid;
* constructional maps preserve precision and compose on safely transported
  states;
* safe transport invalidates blame, whereas an explicit reflection capability
  transports it functorially;
* revision activation commutes with construction, dependent construction, and
  evidence transport;
* proof-relevant naturality squares commute on every safely transported state;
* an undemanded checked plan runs by raw erasure, first demand evaluates once,
  and revision staleness returns only the optional capability to suspension.

The domain instances are the existing cumulative Pi/Sigma/identity
constructors, proof-relevant interaction paths, source-preserving program
islands, and certified parallel rho worlds.  Dependent second-Sigma beta keeps
its two conversion receipts and therefore remains at its explicit higher-cell
boundary; this guarantee does not identify proof trees by proof irrelevance.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.NativeGradualDependentGuarantee

open _root_.CategoryTheory
open Mettapedia.Languages.MeTTa.PrimeCandidates.GradualExecutionPlan
open Mettapedia.Languages.MeTTa.PrimeCandidates.GradualDependentCapability
open Mettapedia.TypeTheory.DisplayedEvidence
open Mettapedia.TypeTheory.DisplayedEvidence.Status
open Mettapedia.TypeTheory.DisplayedEvidence.ExactMap (mapSafe mapReflecting)
open Mettapedia.TypeTheory.DisplayedEvidence.ExactMap
  (SafeTransportLaws ReflectingTransportLaws SafeSquareLaws safeTransportLaws
   reflectingTransportLaws safeSquareLaws identityReflectingTransportLaws
   mapSafe_comp mapSafe_id_refines mapReflecting_id mapReflecting_comp
   mapSafe_activateAt mapReflecting_activateAt)

universe uRaw uExact uRaw' uExact' uRaw'' uExact'' uRevision uKey uCell
  uRetry uTy uOutput

/-! ## Lazy demand and raw execution -/

/-- A checked capability executes by raw erasure with no checker parameter in
the runner.  The typing relation is arbitrary because the checked branch does
not inspect it. -/
theorem checked_run_is_raw
    {fibre : Family.{uRaw, uExact}}
    {Key : Type uKey} {Ty : Type uTy}
    {HasType : fibre.Raw -> Ty -> Prop}
    {Output : Type uOutput}
    (key : Key) (raw : fibre.Raw) (runRaw : fibre.Raw -> Output) :
    (Plan.checked (Ty := Ty) (HasType := HasType)
      (Mettapedia.Languages.MeTTa.PrimeCandidates.GradualDependentCapability.checkedPlan
        (fibre := fibre) key raw)).run
        runRaw = runRaw raw :=
  rfl

/-- Current demand information may be used, while the identical cached state
at a stale revision becomes suspension.  In both cases the raw index is the
same by construction. -/
theorem demand_revision_dichotomy
    {fibre : Family.{uRaw, uExact}} {Retry : Type uRetry}
    (checker :
      Mettapedia.Languages.MeTTa.PrimeCandidates.GradualDependentCapability.Checker
        fibre Retry)
    (raw : fibre.Raw) {Revision : Type uRevision} [DecidableEq Revision]
    (cached current : Revision) :
    (cached = current ->
      (checker.demandState raw).activateAt cached current =
        checker.demandState raw) /\
    (cached ≠ current ->
      (checker.demandState raw).activateAt cached current =
        (Status.suspended : Status (Reason := List Nat) fibre raw)) := by
  constructor
  · intro same
    subst current
    simp
  · intro stale
    exact activateAt_stale stale _

/-- The full generic lazy guarantee at one boundary: demand can only refine
suspension, and its first evaluation count is exactly one. -/
theorem demand_refines_once
    {fibre : Family.{uRaw, uExact}} {Retry : Type uRetry}
    (checker :
      Mettapedia.Languages.MeTTa.PrimeCandidates.GradualDependentCapability.Checker
        fibre Retry)
    {Key : Type uKey} {Cell : Type uCell}
    (key : Key) (raw : fibre.Raw) (cell : Cell) :
    Refines (checker.demandState raw)
        (.suspended : Status (Reason := List Nat) fibre raw) /\
      ((Mettapedia.Languages.MeTTa.PrimeCandidates.GradualDependentCapability.checkedPlan
        (fibre := fibre) key raw).demandCheck checker.toNeedChecker cell).2.evaluationCount = 1 :=
  ⟨checker.demandState_refines_suspended raw,
    Mettapedia.Languages.MeTTa.PrimeCandidates.GradualDependentCapability.demandCheck_evaluationCount
      checker key raw cell⟩

/-! ## Domain-level controls and the higher boundary -/

open Mettapedia.Languages.MeTTa.PrimeCandidates.NativeGradualDependentNaturality
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.SyntacticContextual
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.SyntacticJudgmentalPi
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.SyntacticJudgmentalSigmaId

/-- Formed-context substitution receives its gradual laws from the generic
constructional interface. -/
theorem formedSubstitutionSafeTransportLaws
    {Head : Type} {rules : Rules Head}
    {source target : FormedContext rules} (morphism : source ⟶ target) :
    SafeTransportLaws (Reason := List Nat) (reindexJudgmentMap morphism) :=
  safeTransportLaws _

/-- Proof-relevant GSLT-IL interaction transport receives the same laws; its
raw endpoint path remains present when occurrence evidence is unavailable. -/
theorem interactionSafeTransportLaws
    {theory targetTheory : Mettapedia.GSLT.GSLT}
    (presentation : Mettapedia.GSLT.Core.InteractionEvent.InteractionPresentation theory)
    (translation :
      Mettapedia.GSLT.IndexedOperational.OperationalTranslation theory targetTheory)
    {source target : theory.Term} :
    SafeTransportLaws (Reason := List Nat)
      (Mettapedia.Languages.MeTTa.PrimeCandidates.NativeGradualDependentInteraction.transportMap
        presentation translation (source := source) (target := target)) :=
  safeTransportLaws _

/-- The cumulative candidate lambda naturality square is an earned safe gradual
square, not an independently postulated gradual rule. -/
theorem lambdaSafeSquareLaws
    {Head : Type}
    {rules : Rules Head}
    {source target : FormedContext rules}
    {domain : TypeOver target}
    {codomain : TypeOver (extendContext target domain)}
    (product : DependentProduct domain codomain)
    (morphism : source ⟶ target) :
    SafeSquareLaws (Reason := List Nat) (lambdaNaturalitySquare product morphism) :=
  safeSquareLaws _

/-- The existing non-reflecting collapse is the permanent negative control:
safe transport exists, but stable blame transport cannot be manufactured. -/
theorem forward_transport_does_not_imply_reflection :
    Not (Nonempty
      Mettapedia.Languages.MeTTa.PrimeCandidates.GradualDependentCapability.Canary.collapse.ReflectsExact) :=
  Mettapedia.Languages.MeTTa.PrimeCandidates.GradualDependentCapability.Canary.collapse_not_reflects

/-- The capability hierarchy is strict: the collapse earns all forward-safe
laws but cannot earn reflection and therefore cannot soundly retain blame. -/
theorem safe_transport_strictly_below_reflecting :
    SafeTransportLaws (Reason := List Nat)
        Mettapedia.Languages.MeTTa.PrimeCandidates.GradualDependentCapability.Canary.collapse /\
      Not (Nonempty
        Mettapedia.Languages.MeTTa.PrimeCandidates.GradualDependentCapability.Canary.collapse.ReflectsExact) :=
  ⟨safeTransportLaws _, forward_transport_does_not_imply_reflection⟩

/-- Dependent second-Sigma beta cannot be collapsed to a homogeneous equality
step: its source and target type codes are genuinely different. -/
theorem dependent_beta_requires_conversion_dimension :
    ((sigmaSecondBetaMap Canary.sigmaRetainedTower
      Mettapedia.Languages.MeTTa.PrimeCandidates.NativeGradualDependentTermFormers.Canary.dependentSum).mapRaw
      Mettapedia.Languages.MeTTa.PrimeCandidates.NativeGradualDependentTermFormers.Canary.dependentPairInput).sourceType ≠
    ((sigmaSecondBetaMap Canary.sigmaRetainedTower
      Mettapedia.Languages.MeTTa.PrimeCandidates.NativeGradualDependentTermFormers.Canary.dependentSum).mapRaw
      Mettapedia.Languages.MeTTa.PrimeCandidates.NativeGradualDependentTermFormers.Canary.dependentPairInput).targetType :=
  Canary.dependentSigmaSecondBeta_sourceType_ne_targetType

/-! ## Axiom audit -/

#print axioms Mettapedia.TypeTheory.DisplayedEvidence.Status.Refines.toSuspended
#print axioms Mettapedia.TypeTheory.DisplayedEvidence.ExactMap.mapSafe_comp
#print axioms Mettapedia.TypeTheory.DisplayedEvidence.ExactMap.mapReflecting_comp
#print axioms Mettapedia.TypeTheory.DisplayedEvidence.ExactMap.mapSafe_activateAt
#print axioms Mettapedia.TypeTheory.DisplayedEvidence.Status.combineDependent_activateAt
#print axioms Mettapedia.TypeTheory.DisplayedEvidence.ExactMap.safeTransportLaws
#print axioms Mettapedia.TypeTheory.DisplayedEvidence.ExactMap.reflectingTransportLaws
#print axioms Mettapedia.TypeTheory.DisplayedEvidence.ExactMap.identityReflectingTransportLaws
#print axioms Mettapedia.TypeTheory.DisplayedEvidence.ExactMap.safeSquareLaws
#print axioms checked_run_is_raw
#print axioms demand_revision_dichotomy
#print axioms demand_refines_once
#print axioms lambdaSafeSquareLaws
#print axioms formedSubstitutionSafeTransportLaws
#print axioms interactionSafeTransportLaws
#print axioms forward_transport_does_not_imply_reflection
#print axioms safe_transport_strictly_below_reflecting
#print axioms dependent_beta_requires_conversion_dimension

end Mettapedia.Languages.MeTTa.PrimeCandidates.NativeGradualDependentGuarantee
