import Mettapedia.Languages.MeTTa.PrimeCandidates.Native.GradualExecutionPlan
import Mettapedia.TypeTheory.DisplayedEvidence
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.SyntacticContextualCategory

/-!
# Need checking for displayed native evidence

The generic family, live evidence status, precision relation and constructional
maps are those of `TypeTheory.DisplayedEvidence`. A path-labelled refutation
uses `List Nat` as its reason type. This module supplies the concrete adapter
to the existing checked Need plan and instantiates it with formed judgments
of the parameterized Pi/Sigma/Id calculus.

Demand retains the exact raw index in successful, refuted and retryable
payloads. Typed substitution transports evidence; refutation transport also
requires reflection. The positive and separating negative controls exercise
these operations on the same retained raw values.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.GradualDependentCapability

open _root_.CategoryTheory
open Mettapedia.GSLT.Dynamics
open Mettapedia.TypeTheory.DisplayedEvidence
open Mettapedia.TypeTheory.DisplayedEvidence.Status
open Mettapedia.TypeTheory.DisplayedEvidence.ExactMap (mapSafe mapReflecting)
open Mettapedia.Languages.MeTTa.PrimeCandidates.GradualExecutionPlan
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.SyntacticContextual

universe uRaw uExact uKey uRetry uCell uRevision uTy

variable {fibre : Family.{uRaw, uExact}} {raw : fibre.Raw}

/-! ## Demand through the existing Need protocol -/

/-- A dependent check result is indexed by the exact raw value it decided. -/
inductive Decision (fibre : Family.{uRaw, uExact}) (Retry : Type uRetry)
    (raw : fibre.Raw) where
  | established (evidence : fibre.Exact raw)
  | refuted (blame : Refutation (Reason := List Nat) fibre raw)
  | retry (reason : Retry)

/-- A boundary checker decides a displayed capability for each raw value. -/
structure Checker (fibre : Family.{uRaw, uExact}) (Retry : Type uRetry) where
  check : (raw : fibre.Raw) -> Decision fibre Retry raw

structure EvidenceBundle (fibre : Family.{uRaw, uExact}) where
  raw : fibre.Raw
  evidence : fibre.Exact raw

abbrev BlameBundle (fibre : Family.{uRaw, uExact}) :=
  Sigma (Refutation (Reason := List Nat) fibre)

abbrev RetryBundle (fibre : Family.{uRaw, uExact}) (Retry : Type uRetry) :=
  fibre.Raw × Retry

/-- Forget the dependent result into the existing uniform Need outcome.  The
raw index is retained in every payload. -/
def Checker.toNeedChecker {fibre : Family.{uRaw, uExact}}
    {Retry : Type uRetry} (checker : Checker fibre Retry) :
    GradualExecutionPlan.Checker fibre.Raw (EvidenceBundle fibre)
      (BlameBundle fibre) (RetryBundle fibre Retry) where
  check raw :=
    match checker.check raw with
    | .established evidence => .value ⟨raw, evidence⟩
    | .refuted blame => .stableFault ⟨raw, blame⟩
    | .retry reason => .retryableFault (raw, reason)

/-- The dependent view of the state produced by one demand. -/
def Checker.demandState {fibre : Family.{uRaw, uExact}}
    {Retry : Type uRetry} (checker : Checker fibre Retry)
    (raw : fibre.Raw) : Status (Reason := List Nat) fibre raw :=
  match checker.check raw with
  | .established evidence => .established evidence
  | .refuted blame => .refuted blame
  | .retry _ => .suspended

theorem Checker.demandState_refines_suspended
    {fibre : Family.{uRaw, uExact}} {Retry : Type uRetry}
    (checker : Checker fibre Retry) (raw : fibre.Raw) :
    Refines (checker.demandState raw) (.suspended : Status (Reason := List Nat) fibre raw) := by
  unfold Checker.demandState
  split
  · exact .established_suspended _
  · exact .refuted_suspended _
  · exact .refl _

/-- A checked dependent capability is an ordinary checked plan whose raw
term and obligation are the same indexed value. -/
def checkedPlan {fibre : Family.{uRaw, uExact}} {Key : Type uKey}
    (key : Key) (raw : fibre.Raw) :
    CheckedPlan fibre.Raw Key fibre.Raw where
  term := raw
  origin := ⟨key, raw⟩

@[simp] theorem checkedPlan_runs_raw {fibre : Family.{uRaw, uExact}}
    {Key : Type uKey} {Ty : Type uTy}
    {HasType : fibre.Raw -> Ty -> Prop} (key : Key) (raw : fibre.Raw) :
    (Plan.checked (Ty := Ty) (HasType := HasType)
      (checkedPlan (fibre := fibre) key raw)).run id = raw :=
  rfl

/-- The uniform Need target produced by demand is exactly the bundled form of
the dependent demand state. -/
theorem demandCheck_target_eq
    {fibre : Family.{uRaw, uExact}} {Key : Type uKey}
    {Retry : Type uRetry} (checker : Checker fibre Retry)
    (key : Key) (raw : fibre.Raw) (cell : Cell) :
    ((checkedPlan (fibre := fibre) key raw).demandCheck
      checker.toNeedChecker cell).1 =
      match checker.demandState raw with
      | .suspended => .suspended (CheckOrigin.mk key raw)
      | .established evidence =>
          .cachedValue (CheckOrigin.mk key raw) ⟨raw, evidence⟩
      | .refuted blame =>
          .cachedStableFault (CheckOrigin.mk key raw) ⟨raw, blame⟩ := by
  cases outcome : checker.check raw <;>
    simp [CheckedPlan.demandCheck, Checker.toNeedChecker,
      Checker.demandState, checkedPlan, outcome]

/-- Demand performs exactly one evaluation in the established Need model. -/
theorem demandCheck_evaluationCount
    {fibre : Family.{uRaw, uExact}} {Key : Type uKey}
    {Retry : Type uRetry} (checker : Checker fibre Retry)
    (key : Key) (raw : fibre.Raw) (cell : Cell) :
    ((checkedPlan (fibre := fibre) key raw).demandCheck
      checker.toNeedChecker cell).2.evaluationCount = 1 :=
  CheckedPlan.demandCheck_evaluationCount _ _ _

/-! ## Formed candidate judgments as a dependent instance -/

namespace FormedJudgment

/-- A raw formed-judgment candidate retains its proposed type and term but no
typing evidence. -/
structure Raw {rules : Rules Head} (context : FormedContext rules) where
  type : TypeOver context
  term : Tm Head context.arity

/-- Exact evidence is the existing declaration-aware typing judgment. -/
def judgmentFibre {rules : Rules Head}
    (context : FormedContext rules) : Family where
  Raw := Raw context
  Exact := fun candidate =>
    PLift (HasType rules context.context candidate.term candidate.type.code)

/-- Typed context substitution is a constructional exact map. -/
def reindexMap {rules : Rules Head}
    {source target : FormedContext rules} (morphism : source ⟶ target) :
    ExactMap (judgmentFibre target) (judgmentFibre source) where
  mapRaw := fun candidate =>
    { type := candidate.type.reindex morphism
      term := subst morphism.substitution candidate.term }
  mapExact := fun evidence => ⟨by
    change HasType rules source.context
      (subst morphism.substitution _)
      (subst morphism.substitution _)
    exact evidence.down.substitute morphism.typed⟩

/-- Substitution transports positive typing evidence without invoking a
checker. -/
@[simp] theorem reindex_exact {rules : Rules Head}
    {source target : FormedContext rules} (morphism : source ⟶ target)
    (candidate : Raw target)
    (evidence : (judgmentFibre target).Exact candidate) :
    mapSafe (Reason := List Nat) (reindexMap morphism) (.established evidence) =
      .established ((reindexMap morphism).mapExact evidence) :=
  ExactMap.mapSafe_established _ _

/-- In the absence of a reflection theorem, a cached source-context
refutation is invalidated by substitution. -/
@[simp] theorem reindex_refuted_invalidates {rules : Rules Head}
    {source target : FormedContext rules} (morphism : source ⟶ target)
    (candidate : Raw target)
    (blame : Refutation (Reason := List Nat) (judgmentFibre target) candidate) :
    mapSafe (reindexMap morphism) (.refuted blame) = .suspended :=
  ExactMap.mapSafe_refuted _ _

/-- If a particular substitution reflects typing on the named candidate,
stable blame can be transported as well. -/
def reindexFull {rules : Rules Head}
    {source target : FormedContext rules} (morphism : source ⟶ target)
    (reflects : (reindexMap morphism).ReflectsExact)
    {candidate : Raw target} :
    Status (Reason := List Nat) (judgmentFibre target) candidate ->
      Status (Reason := List Nat) (judgmentFibre source) ((reindexMap morphism).mapRaw candidate) :=
  mapReflecting (reindexMap morphism) reflects

end FormedJudgment

/-! ## Positive and negative controls -/

namespace Canary

/-- A small source fibre with one supported and one unsupported raw value. -/
def source : Family where
  Raw := Bool
  Exact := fun value => PLift (value = true)

/-- The target forgets the source distinction and accepts its sole value. -/
def target : Family where
  Raw := PUnit
  Exact := fun _ => PUnit

def collapse : ExactMap source target where
  mapRaw := fun _ => PUnit.unit
  mapExact := fun _ => PUnit.unit

def supported : Status (Reason := List Nat) source true := .established ⟨rfl⟩

theorem supported_maps_exact :
    mapSafe collapse supported = .established PUnit.unit :=
  rfl

def unsupportedBlame : Refutation (Reason := List Nat) source false where
  reason := [0]
  refutes := by
    intro impossible
    exact Bool.false_ne_true impossible.down

/-- Negative evidence is invalidated rather than smuggled through a
non-reflecting collapse. -/
theorem unsupported_blame_invalidates :
    mapSafe collapse (.refuted unsupportedBlame) = .suspended :=
  rfl

/-- The collapse really does not reflect exact evidence: its target accepts
the image of the unsupported source point. -/
theorem collapse_not_reflects : ¬ Nonempty collapse.ReflectsExact := by
  rintro ⟨reflects⟩
  have impossible : PLift (false = true) :=
    reflects.reflect (raw := false) PUnit.unit
  exact Bool.false_ne_true impossible.down

theorem stale_supported_falls_back :
    supported.activateAt (0 : Nat) 1 = .suspended := by
  exact activateAt_stale (by decide) supported

theorem current_supported_remains_exact :
    supported.activateAt (1 : Nat) 1 = supported :=
  activateAt_current 1 supported

end Canary

#print axioms Checker.demandState_refines_suspended
#print axioms demandCheck_target_eq
#print axioms demandCheck_evaluationCount
#print axioms FormedJudgment.reindex_exact
#print axioms FormedJudgment.reindex_refuted_invalidates
#print axioms Canary.collapse_not_reflects

end Mettapedia.Languages.MeTTa.PrimeCandidates.GradualDependentCapability
