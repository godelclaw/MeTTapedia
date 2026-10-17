import Mettapedia.GSLT.LanguageDef.CertificateGSLTRootBuchiAuthority
import Mettapedia.GSLT.LanguageDef.CertificateGSLTRecurrentTraceAuthority
import Mettapedia.GSLT.LanguageDef.CheckerAuthorityFamily
import Mettapedia.Logic.PresburgerUniversal

/-!
# Two concrete standard-semantic authorities in one dependent family

The recurrent profile checks a finite invariant region and progress ranks for
one selected controller.  The arithmetic profile decides universally
quantified affine inequalities over the standard natural numbers.  The same
existing authority dispatcher retains their different claims, evidence and
meanings, and refuses cross-profile evidence.

For GSLT controllers, accepted local edge certificates additionally establish
that every selected transition is a genuine source step.  The certificate
scope remembers acceptance of those particular local witnesses; arbitrary
true source edges do not make invalid supplied witnesses acceptable.
-/

namespace Mettapedia.GSLT.LanguageDef.StandardSemanticAuthorityProfiles

open Mettapedia.GSLT
open CertificateGSLT KernelAuthority CheckerAuthorityFamily
open Mettapedia.Logic

universe uState uAction uAuthority uCertificate

/-- The existing root recurrence checker at the common checker interface. -/
def rootChecker {State : Type uState} {Action : Type uAction} [Fintype State]
    (system : LabeledSystem State Action) :
    Checker (BuchiControllerClaim State Action) (RootBuchiCertificate State) where
  check := fun claim certificate => certificate.check system claim

theorem rootChecker_authority
    {State : Type uState} {Action : Type uAction} [Fintype State]
    (system : LabeledSystem State Action) :
    (rootChecker system).Authority (BuchiControllerClaim.RootMeaning system) where
  sound := by
    intro claim certificate accepted
    exact certificate.check_sound accepted
  complete := by
    intro claim meaning
    exact RootBuchiCertificate.exists_of_meaning meaning

/-- The arithmetic algorithm is a decision kernel, rather than only a
semi-decision procedure enumerating candidate certificates. -/
def affineDecision (nVars : Nat) :
    Checker.DecisionKernel (PresburgerUniversal.Claim nVars)
      PresburgerUniversal.Claim.Meaning where
  decide := PresburgerUniversal.Claim.check
  correct := PresburgerUniversal.Claim.check_eq_true_iff

inductive Kind where
  | rootRecurrence
  | universalAffine
deriving DecidableEq, Repr

/-- These concrete profiles plug into the existing dependent authority
family.  Both certified scopes equal their stated standard meanings. -/
def family {State Action : Type} [Fintype State]
    (system : LabeledSystem State Action) (nVars : Nat) : AuthorityFamily Kind where
  Claim
    | .rootRecurrence => BuchiControllerClaim State Action
    | .universalAffine => PresburgerUniversal.Claim nVars
  Certificate
    | .rootRecurrence => RootBuchiCertificate State
    | .universalAffine => Unit
  checker
    | .rootRecurrence => rootChecker system
    | .universalAffine => (affineDecision nVars).toChecker
  Certified
    | .rootRecurrence => BuchiControllerClaim.RootMeaning system
    | .universalAffine => PresburgerUniversal.Claim.Meaning
  Meaning
    | .rootRecurrence => BuchiControllerClaim.RootMeaning system
    | .universalAffine => PresburgerUniversal.Claim.Meaning
  projection
    | .rootRecurrence =>
        { authority := rootChecker_authority system
          project := fun _ meaningful => meaningful }
    | .universalAffine =>
        { authority := (affineDecision nVars).authority
          project := fun _ meaningful => meaningful }

/-- The combined dispatcher is exact for the disjoint union of the two
independently defined standard meanings. -/
theorem packed_exists_iff_meaning {State Action : Type} [Fintype State]
    (system : LabeledSystem State Action) (nVars : Nat)
    (claim : (family system nVars).PackedClaim) :
    (∃ certificate, (family system nVars).packedChecker.check claim certificate = true) ↔
      (family system nVars).packedMeaning claim := by
  obtain ⟨kind, claim⟩ := claim
  cases kind <;>
    exact ((family system nVars).packedChecker_authority.meaning_iff_exists_certificate _).symm

/-- Convert the existing recurrent trace claim without changing its selected
states, actions or root. -/
def rootClaim {theory : GSLT}
    {StepCertificate : Type uCertificate}
    (claim : RecurrentTraceClaim theory StepCertificate) :
    BuchiControllerClaim theory.Term (TraceLink theory StepCertificate) where
  root := claim.root
  controller := claim.controller

/-- Replay of source-edge witnesses connects the controller recurrence
certificate to genuine infinite GSLT execution. -/
theorem rootChecker_gslt_sound
    {AuthorityId : Type uAuthority} {theory : GSLT}
    [Fintype theory.Term] [DecidableEq theory.Term]
    (stepAuthority : StepAuthority.{uAuthority, uCertificate} AuthorityId theory)
    (accepting : theory.Term → Bool)
    {claim : RecurrentTraceClaim theory stepAuthority.Certificate}
    {certificate : RootBuchiCertificate theory.Term}
    (checked : certificate.check (auditedLabeledSystem stepAuthority accepting)
      (rootClaim claim) = true) :
    claim.Meaning accepting := by
  have meaning := certificate.check_sound checked
  intro execution
  constructor
  · intro index
    have sourceEdge := (meaning.1 index).2
    have actual := auditedLabeledSystem_step_sound stepAuthority accepting sourceEdge
    simpa [rootClaim, execution.state_eq_iterate,
      Function.iterate_succ_apply'] using actual
  · exact meaning.2 execution

/-- The exact local-witness scope projects to actual source execution.  This
does not erase failures of the supplied local edge certificates. -/
theorem rootGSLTProjection
    {AuthorityId : Type uAuthority} {theory : GSLT}
    [Fintype theory.Term] [DecidableEq theory.Term]
    (stepAuthority : StepAuthority.{uAuthority, uCertificate} AuthorityId theory)
    (accepting : theory.Term → Bool) :
    ({ check := fun claim certificate =>
        certificate.check (auditedLabeledSystem stepAuthority accepting)
          (rootClaim claim) } :
      Checker (RecurrentTraceClaim theory stepAuthority.Certificate)
        (RootBuchiCertificate theory.Term)).AuthorityProjection
      (fun claim => (rootClaim claim).RootMeaning
        (auditedLabeledSystem stepAuthority accepting))
      (RecurrentTraceClaim.Meaning accepting) where
  authority :=
    { sound := by
        intro claim certificate checked
        exact certificate.check_sound checked
      complete := by
        intro claim meaning
        exact RootBuchiCertificate.exists_of_meaning meaning }
  project := by
    intro claim meaningful
    obtain ⟨certificate, checked⟩ := RootBuchiCertificate.exists_of_meaning meaningful
    exact rootChecker_gslt_sound stepAuthority accepting checked

namespace Controls

def splitSystem : LabeledSystem Bool Unit where
  step source _ target := decide (target = source)
  accepting := id

def stayController : MemorylessController Bool Unit where
  active _ := true
  action _ := ()
  next := id

def acceptedRoot : BuchiControllerClaim Bool Unit := ⟨true, stayController⟩
def rejectedRoot : BuchiControllerClaim Bool Unit := ⟨false, stayController⟩

def acceptingRegion : RootBuchiCertificate Bool where
  region := id
  progress.rank _ := 0

def wholeRegion : RootBuchiCertificate Bool where
  region _ := true
  progress.rank _ := 0

theorem accepting_root_checked : acceptingRegion.check splitSystem acceptedRoot = true := by
  decide

theorem unreachable_bad_component_excluded :
    acceptingRegion.check splitSystem acceptedRoot = true ∧
      wholeRegion.check splitSystem acceptedRoot = false := by
  decide

theorem true_root_has_standard_meaning : acceptedRoot.RootMeaning splitSystem :=
  acceptingRegion.check_sound accepting_root_checked

/-- The old whole-region progress language cannot certify this controller,
although its selected accepting root has the desired standard meaning. -/
theorem no_whole_region_progress :
    ¬ ∃ measure : ProgressMeasure Bool,
      measure.Valid splitSystem stayController true := by
  rintro ⟨measure, valid⟩
  have impossible := valid.2 false (by rfl)
  simp [splitSystem, stayController] at impossible

theorem bad_root_has_no_certificate :
    ¬ ∃ certificate : RootBuchiCertificate Bool,
      certificate.check splitSystem rejectedRoot = true := by
  rintro ⟨certificate, accepted⟩
  have meaning := certificate.check_sound accepted
  have recurrent := (stayController.buchi_iff_canonical splitSystem false).mp meaning.2
  obtain ⟨visit, _, accepts⟩ := recurrent 0
  simp [splitSystem, stayController] at accepts

/-- Both successors are permitted, but the controller selects only its
accepting self-loop. -/
def branchingSystem : LabeledSystem Bool Unit where
  step _ _ _ := true
  accepting := id

def escapingPath (index : Nat) : Bool := decide (index = 0)

theorem selected_recurrence_does_not_cover_all_system_paths :
    acceptingRegion.check branchingSystem acceptedRoot = true ∧
    escapingPath 0 = true ∧
    (∀ index, branchingSystem.step (escapingPath index) ()
      (escapingPath (index + 1)) = true) ∧
    ¬ InfinitelyOftenAccepting branchingSystem escapingPath := by
  refine ⟨by decide, rfl, fun _ => rfl, ?_⟩
  intro recurrent
  obtain ⟨visit, after, accepts⟩ := recurrent 1
  have zero : visit = 0 := of_decide_eq_true accepts
  omega

def toggleTheory : GSLT where
  Term := Bool
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites source target := target = !source
  rewrites_resp_left := by
    intro source other target equal step
    subst other
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target other step equal
    exact equal ▸ step

instance : Fintype toggleTheory.Term := inferInstanceAs (Fintype Bool)
instance : DecidableEq toggleTheory.Term := inferInstanceAs (DecidableEq Bool)

def toggleEdgeAuthority : StepAuthority String toggleTheory where
  id := "boolean-toggle-v1"
  Certificate := Bool
  check claim witness := witness &&
    @decide ((claim.target : Bool) = !claim.source) (Bool.decEq claim.target (!claim.source))
  sound := by
    intro claim witness accepted
    simp only [Bool.and_eq_true] at accepted
    exact @of_decide_eq_true _ (Bool.decEq claim.target (!claim.source)) accepted.2

def toggleClaim : RecurrentTraceClaim toggleTheory Bool where
  root := false
  controller :=
    { active := fun _ => true
      action := fun state => ⟨!state, true⟩
      next := Bool.not }

def toggleCertificate : RootBuchiCertificate Bool where
  region _ := true
  progress.rank state := if state then 0 else 1

theorem toggle_checked :
    toggleCertificate.check (auditedLabeledSystem toggleEdgeAuthority id)
      (rootClaim toggleClaim) = true := by
  decide

theorem toggle_is_genuine_recurrent_source_execution : toggleClaim.Meaning id :=
  rootChecker_gslt_sound toggleEdgeAuthority id toggle_checked

/-- The actual next-state sequence is unchanged, but the attached edge
evidence is false and must be rejected. -/
def badWitnessClaim : RecurrentTraceClaim toggleTheory Bool where
  root := false
  controller := { toggleClaim.controller with action := fun state => ⟨!state, false⟩ }

theorem bad_witnesses_rejected :
    toggleCertificate.check (auditedLabeledSystem toggleEdgeAuthority id)
      (rootClaim badWitnessClaim) = false := by
  decide

theorem bad_witnesses_do_not_change_underlying_path_truth : badWitnessClaim.Meaning id := by
  intro execution
  exact toggle_is_genuine_recurrent_source_execution
    { state := execution.state, starts := execution.starts, follows := execution.follows }

open FirstOrder

def increasingAffine : PresburgerUniversal.Claim 1 where
  left := (Language.Term.var 0 + Language.Term.var 0) + 1
  right := (Language.Term.var 0 + Language.Term.var 0) + Language.Term.var 0 + 4

def eventuallyFalseAffine : PresburgerUniversal.Claim 1 where
  left := (Language.Term.var 0 + Language.Term.var 0) + Language.Term.var 0
  right := (Language.Term.var 0 + Language.Term.var 0) + 10

theorem affine_positive : increasingAffine.check = true := by decide
theorem affine_negative : eventuallyFalseAffine.check = false := by decide

theorem affine_positive_all_naturals : increasingAffine.Meaning :=
  increasingAffine.check_eq_true_iff.mp affine_positive

theorem affine_negative_has_countervaluation :
    ∃ valuation : Fin 1 → Nat, eventuallyFalseAffine.right.realize valuation <
      eventuallyFalseAffine.left.realize valuation :=
  eventuallyFalseAffine.refused_iff_counterexample.mp affine_negative

theorem affine_countervaluation_eleven :
    eventuallyFalseAffine.right.realize (fun _ => (11 : Nat)) <
      eventuallyFalseAffine.left.realize (fun _ => (11 : Nat)) := by decide

def profiles := family splitSystem 1

theorem packed_buchi_positive :
    profiles.packedChecker.check ⟨.rootRecurrence, acceptedRoot⟩
      ⟨.rootRecurrence, acceptingRegion⟩ = true := by decide

theorem packed_arithmetic_positive :
    profiles.packedChecker.check ⟨.universalAffine, increasingAffine⟩
      ⟨.universalAffine, ()⟩ = true := by decide

theorem cross_profile_evidence_refused :
    profiles.packedChecker.check ⟨.rootRecurrence, acceptedRoot⟩
      ⟨.universalAffine, ()⟩ = false := by decide

/-- Executable controls exercise the original checkers and their shared
dependent dispatcher.  Each Boolean records agreement with its stated verdict. -/
def runtimeControls : List (String × Bool) :=
  [ ("accepting root", acceptingRegion.check splitSystem acceptedRoot)
  , ("unreachable bad component included", !wholeRegion.check splitSystem acceptedRoot)
  , ("bad root", !wholeRegion.check splitSystem rejectedRoot)
  , ("root omitted", !acceptingRegion.check splitSystem rejectedRoot)
  , ("selected branch", acceptingRegion.check branchingSystem acceptedRoot)
  , ("genuine GSLT toggle", toggleCertificate.check
      (auditedLabeledSystem toggleEdgeAuthority id) (rootClaim toggleClaim))
  , ("invalid local edge evidence", !toggleCertificate.check
      (auditedLabeledSystem toggleEdgeAuthority id) (rootClaim badWitnessClaim))
  , ("universal natural inequality", increasingAffine.check)
  , ("eventually false inequality", !eventuallyFalseAffine.check)
  , ("packed recurrence", profiles.packedChecker.check
      ⟨.rootRecurrence, acceptedRoot⟩ ⟨.rootRecurrence, acceptingRegion⟩)
  , ("packed arithmetic", profiles.packedChecker.check
      ⟨.universalAffine, increasingAffine⟩ ⟨.universalAffine, ()⟩)
  , ("wrong profile", !profiles.packedChecker.check
      ⟨.rootRecurrence, acceptedRoot⟩ ⟨.universalAffine, ()⟩) ]

theorem runtimeControls_all_pass : runtimeControls.all Prod.snd = true := by decide

end Controls

end Mettapedia.GSLT.LanguageDef.StandardSemanticAuthorityProfiles
