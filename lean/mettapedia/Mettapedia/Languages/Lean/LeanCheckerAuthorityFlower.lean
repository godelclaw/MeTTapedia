import Mettapedia.GSLT.LanguageDef.KernelCheckingClasses
import Mettapedia.Languages.Lean.Lean4LeanRungOneDeltaDecision

/-!
# Authority edges for Lean-family checkers

Lean-family checking services expose several logically different contracts.
An exact decision procedure characterizes a judgment in both directions.  A
semantically justified external checker may instead provide only the forward
edge from an accepted output to a model.  An optimized checker may reach that
edge through a one-way simulation into a pure checker.  Agreement between two
executables is useful differential evidence, but supplies no semantic edge by
itself.

This module makes those edge kinds explicit and proves their composition and
separation laws.  The four outcomes retain the distinction between rejecting
an invalid input, declining an unsupported input, and an operational error.
Only `accepted` carries authority.

The concrete instance at the end uses the existing executable beta/delta/head
fragment over Lean4Lean syntax.  No external whole-Lean checker is imported or
claimed to satisfy these interfaces here.
-/

namespace Mettapedia.Languages.Lean.LeanCheckerAuthorityFlower

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.Framework.LanguageIndexedModalFunctor
open Mettapedia.Languages.Lean.Lean4LeanDirectedReduction
open Mettapedia.Languages.Lean.Lean4LeanRungOneDeltaDecision

universe uInput uOutput uModel uCertificate

/-! ## Four-outcome services -/

/-- The public result of a partial checking service.  Refusal, unsupported
input, and operational failure remain distinct non-accepting outcomes. -/
inductive Outcome (Output : Type uOutput) where
  | accepted (output : Output)
  | rejected
  | declined
  | error
  deriving DecidableEq, Repr

/-- A checking service may return a checked result or one of three distinct
non-accepting outcomes. -/
structure Service (Input : Type uInput) (Output : Type uOutput) where
  run : Input → Outcome Output

namespace Service

/-- Acceptance retains the exact output whose authority is being claimed. -/
def Accepts (service : Service Input Output) (input : Input) (output : Output) : Prop :=
  service.run input = .accepted output

/-- Some output was accepted.  This forgets its identity only explicitly. -/
def AcceptsSome (service : Service Input Output) (input : Input) : Prop :=
  ∃ output, service.Accepts input output

/-- Semantic soundness is a forward edge from accepted outputs. -/
def Sound (service : Service Input Output)
    (Meaning : Input → Output → Prop) : Prop :=
  ∀ input output, service.Accepts input output → Meaning input output

/-- Model soundness is the particular forward edge from every accepted output
to at least one semantic realization. -/
def ModelSound (service : Service Input Output)
    (Satisfies : Input → Output → Model → Prop) : Prop :=
  ∀ input output, service.Accepts input output →
    ∃ model, Satisfies input output model

/-- A claim is model-forbidden when no possible accepted output has a model. -/
def ModelForbidden (Satisfies : Input → Output → Model → Prop)
    (input : Input) : Prop :=
  ∀ output model, ¬Satisfies input output model

/-- Model soundness prevents acceptance of a model-forbidden input.  It does
not choose between rejection, decline, and error. -/
theorem ModelSound.not_accepts_forbidden
    {service : Service Input Output}
    {Satisfies : Input → Output → Model → Prop}
    (sound : service.ModelSound Satisfies)
    {input : Input} (forbidden : ModelForbidden Satisfies input) :
    ¬service.AcceptsSome input := by
  rintro ⟨output, accepted⟩
  obtain ⟨model, realized⟩ := sound input output accepted
  exact forbidden output model realized

/-- The three non-accepting outcomes are exhaustive. -/
theorem not_acceptsSome_iff
    (service : Service Input Output) (input : Input) :
    ¬service.AcceptsSome input ↔
      service.run input = .rejected ∨
      service.run input = .declined ∨
      service.run input = .error := by
  cases result : service.run input with
  | accepted output =>
      simp [AcceptsSome, Accepts, result]
  | rejected =>
      simp [AcceptsSome, Accepts, result]
  | declined =>
      simp [AcceptsSome, Accepts, result]
  | error =>
      simp [AcceptsSome, Accepts, result]

/-! ## Implementation refinement -/

/-- A one-way implementation refinement maps every accepting implementation
output to an accepting specification output.  It makes no completeness claim. -/
structure AcceptanceRefinement
    (implementation : Service Input Output)
    {SpecificationOutput : Type uModel}
    (specification : Service Input SpecificationOutput) where
  mapOutput : Output → SpecificationOutput
  preserves : ∀ input output, implementation.Accepts input output →
    specification.Accepts input (mapOutput output)

namespace AcceptanceRefinement

variable {implementation : Service Input Output}
  {SpecificationOutput : Type uModel}
  {specification : Service Input SpecificationOutput}

/-- One-way implementation refinement transports ordinary semantic
soundness by reading implementation outputs through the refinement map. -/
theorem sound (refinement :
    AcceptanceRefinement implementation specification)
    {Meaning : Input → SpecificationOutput → Prop}
    (specificationSound : specification.Sound Meaning) :
    implementation.Sound
      (fun input output => Meaning input (refinement.mapOutput output)) := by
  intro input output accepted
  exact specificationSound input (refinement.mapOutput output)
    (refinement.preserves input output accepted)

/-- The cached-to-pure-to-model pattern is composition of two forward edges. -/
theorem modelSound (refinement :
    AcceptanceRefinement implementation specification)
    {Satisfies : Input → SpecificationOutput → Model → Prop}
    (specificationSound : specification.ModelSound Satisfies) :
    implementation.ModelSound
      (fun input output model =>
        Satisfies input (refinement.mapOutput output) model) := by
  intro input output accepted
  exact specificationSound input (refinement.mapOutput output)
    (refinement.preserves input output accepted)

/-- Acceptance refinements compose without turning either forward edge into
an equivalence. -/
def comp
    {FirstOutput : Type uOutput} {SecondOutput : Type uModel}
    {ThirdOutput : Type*}
    {first : Service Input FirstOutput}
    {second : Service Input SecondOutput}
    {third : Service Input ThirdOutput}
    (firstToSecond : AcceptanceRefinement first second)
    (secondToThird : AcceptanceRefinement second third) :
    AcceptanceRefinement first third where
  mapOutput := secondToThird.mapOutput ∘ firstToSecond.mapOutput
  preserves := by
    intro input output accepted
    exact secondToThird.preserves input _
      (firstToSecond.preserves input output accepted)

end AcceptanceRefinement

/-! ## Connection to the common checker authority interface -/

/-- A result-retaining service is a Boolean checker of input/output pairs.
The proposed output is treated as untrusted evidence and recomputed. -/
def pairChecker [DecidableEq Output]
    (service : Service Input Output) :
    Checker (Input × Output) Unit where
  check := fun pair _ => decide (service.run pair.1 = .accepted pair.2)

@[simp] theorem pairChecker_accepts_iff [DecidableEq Output]
    (service : Service Input Output) (input : Input) (output : Output) :
    service.pairChecker.check (input, output) () = true ↔
      service.Accepts input output := by
  simp [pairChecker, Accepts]

/-- Service soundness is exactly common checker soundness on retained
input/output pairs. -/
theorem sound_iff_pairChecker_sound [DecidableEq Output]
    (service : Service Input Output) (Meaning : Input → Output → Prop) :
    service.Sound Meaning ↔
      service.pairChecker.Sound (fun pair => Meaning pair.1 pair.2) := by
  constructor
  · intro sound pair _ accepted
    exact sound pair.1 pair.2
      ((service.pairChecker_accepts_iff pair.1 pair.2).mp accepted)
  · intro sound input output accepted
    exact sound (input, output) ()
      ((service.pairChecker_accepts_iff input output).mpr accepted)

/-- Model soundness therefore becomes a one-way common checker authority
edge.  Certificate completeness is deliberately absent. -/
theorem ModelSound.pairChecker_sound [DecidableEq Output]
    {service : Service Input Output}
    {Satisfies : Input → Output → Model → Prop}
    (sound : service.ModelSound Satisfies) :
    service.pairChecker.Sound
      (fun pair => ∃ model, Satisfies pair.1 pair.2 model) := by
  intro pair _ accepted
  exact sound pair.1 pair.2
    ((service.pairChecker_accepts_iff pair.1 pair.2).mp accepted)

/-! ## Checked reconstruction and elaboration -/

/-- Run an untrusted reconstruction producer and publish its certificate only
after the destination checker accepts it.  Absence of a proposal is a decline;
an invalid proposal is a rejection. -/
def checkedReconstruction
    {Claim : Type uInput} {RawOutput : Type uOutput}
    {Certificate : Type uCertificate}
    (destination : Checker Claim Certificate)
    (propose : Claim → RawOutput → Option Certificate) :
    Service (Claim × RawOutput) Certificate where
  run := fun input =>
    match propose input.1 input.2 with
    | none => .declined
    | some certificate =>
        if destination.check input.1 certificate then
          .accepted certificate
        else
          .rejected

/-- The four-outcome reconstruction service accepts exactly the certificates
published by the existing checked-reconstruction combinator. -/
theorem checkedReconstruction_accepts_iff
    {Claim : Type uInput} {RawOutput : Type uOutput}
    {Certificate : Type uCertificate}
    (destination : Checker Claim Certificate)
    (propose : Claim → RawOutput → Option Certificate)
    (claim : Claim) (raw : RawOutput) (certificate : Certificate) :
    (checkedReconstruction destination propose).Accepts
        (claim, raw) certificate ↔
      destination.reconstruct propose claim raw = some certificate := by
  rw [Checker.reconstruct_eq_some]
  constructor
  · intro accepted
    cases proposed : propose claim raw with
    | none =>
        simp [checkedReconstruction, Accepts, proposed] at accepted
    | some candidate =>
        cases checked : destination.check claim candidate with
        | false =>
            simp [checkedReconstruction, Accepts, proposed, checked] at accepted
        | true =>
            have same : candidate = certificate := by
              simpa [checkedReconstruction, Accepts, proposed, checked] using accepted
            subst certificate
            exact ⟨rfl, checked⟩
  · rintro ⟨proposed, checked⟩
    simp [checkedReconstruction, Accepts, proposed, checked]

/-- Reconstruction needs no trusted producer theorem: destination soundness
alone transports every published certificate to its semantic meaning. -/
theorem checkedReconstruction_sound
    {Claim : Type uInput} {RawOutput : Type uOutput}
    {Certificate : Type uCertificate}
    (destination : Checker Claim Certificate)
    (propose : Claim → RawOutput → Option Certificate)
    {Meaning : Claim → Prop} (sound : destination.Sound Meaning) :
    (checkedReconstruction destination propose).Sound
      (fun input _ => Meaning input.1) := by
  intro input certificate accepted
  exact destination.reconstruct_sound propose sound
    ((checkedReconstruction_accepts_iff destination propose
      input.1 input.2 certificate).mp accepted)

/-- In particular, an accepted reconstructed certificate inherits a model
from the destination checker's independently proved model soundness. -/
theorem checkedReconstruction_modelSound
    {Claim : Type uInput} {RawOutput : Type uOutput}
    {Certificate : Type uCertificate}
    (destination : Checker Claim Certificate)
    (propose : Claim → RawOutput → Option Certificate)
    {Model : Type uModel} {Satisfies : Claim → Model → Prop}
    (sound : destination.Sound (fun claim => ∃ model, Satisfies claim model)) :
    (checkedReconstruction destination propose).ModelSound
      (fun input _ model => Satisfies input.1 model) := by
  intro input certificate accepted
  exact checkedReconstruction_sound destination propose sound
    input certificate accepted

/-! ## Exact decision as one special node -/

/-- Turn an exact one-step decision into a two-outcome service. -/
def ofStepDecision (theory : GSLT)
    (decision : EffectiveStructure.StepDecision theory) :
    Service (theory.Term × theory.Term) Unit where
  run := fun pair =>
    if decision.decideStep pair.1 pair.2 then .accepted () else .rejected

/-- The service retains exactly the Boolean result of its step decision. -/
theorem ofStepDecision_accepts_iff_decide
    (theory : GSLT) (decision : EffectiveStructure.StepDecision theory)
    (source target : theory.Term) :
    (ofStepDecision theory decision).Accepts (source, target) () ↔
      decision.decideStep source target = true := by
  by_cases accepted : decision.decideStep source target = true
  · simp [ofStepDecision, Accepts, accepted]
  · have rejected : decision.decideStep source target = false :=
      Bool.eq_false_of_not_eq_true accepted
    simp [ofStepDecision, Accepts, rejected]

/-- Exact step decisions characterize acceptance in both directions. -/
theorem ofStepDecision_accepts_iff
    (theory : GSLT) (decision : EffectiveStructure.StepDecision theory)
    (source target : theory.Term) :
    (ofStepDecision theory decision).Accepts (source, target) () ↔
      theory.Step source target := by
  exact (ofStepDecision_accepts_iff_decide theory decision source target).trans
    (decision.correct source target)

/-- The actual finite-catalog Lean fragment is an exact service for its
authored raw beta/delta/head judgment. -/
def catalogHeadService {environment : Lean4Lean.VEnv}
    (catalog : DefinitionCatalog environment) (universeParameters : Nat) :
    Service (Lean4Lean.VExpr × Lean4Lean.VExpr) Unit :=
  ofStepDecision (coreRawHeadGSLT environment universeParameters)
    (coreRawStepDecisionOfCatalog catalog universeParameters)

/-- Concrete catalog-service acceptance agrees exactly with the generated
OSLF exact-target predicate. -/
theorem catalogHeadService_accepts_iff_ntt
    {environment : Lean4Lean.VEnv}
    (catalog : DefinitionCatalog environment) (universeParameters : Nat)
    (source target : Lean4Lean.VExpr) :
    (catalogHeadService catalog universeParameters).Accepts
        (source, target) () ↔
      (gsltOSLF (coreRawHeadGSLT environment universeParameters)).satisfies
        source
        (exactCoreRawHeadTargetType environment universeParameters target).pred := by
  exact
    (ofStepDecision_accepts_iff_decide
      (coreRawHeadGSLT environment universeParameters)
      (coreRawStepDecisionOfCatalog catalog universeParameters)
      source target).trans
      (coreRawStepDecisionOfCatalog_accepts_iff_ntt catalog
        universeParameters source target)

/-! ## Separation controls -/

namespace Controls

/-- A nonempty sound service may decline a semantically true input. -/
def soundButIncomplete : Service Bool Unit where
  run
    | false => .accepted ()
    | true => .declined

def everyInputMeaningful (_ : Bool) (_ : Unit) : Prop := True

theorem soundButIncomplete_sound :
    soundButIncomplete.Sound everyInputMeaningful := by
  intro input output accepted
  trivial

theorem meaningful_declined :
    everyInputMeaningful true () ∧
      soundButIncomplete.run true = .declined := by
  exact ⟨trivial, rfl⟩

theorem sound_does_not_imply_completeness :
    soundButIncomplete.Sound everyInputMeaningful ∧
      ¬(∀ input, everyInputMeaningful input () →
        soundButIncomplete.Accepts input ()) := by
  refine ⟨soundButIncomplete_sound, ?_⟩
  intro complete
  have accepted := complete true trivial
  simp [soundButIncomplete, Accepts] at accepted

/-- Two implementations can agree perfectly and still accept a semantically
invalid claim.  Differential agreement is therefore not authority. -/
def agreeingUnsound : Service Bool Unit where
  run _ := .accepted ()

def onlyFalseMeaningful (input : Bool) (_ : Unit) : Prop := input = false

theorem agreement_does_not_imply_soundness :
    (∀ input, agreeingUnsound.run input = agreeingUnsound.run input) ∧
      ¬agreeingUnsound.Sound onlyFalseMeaningful := by
  constructor
  · intro input
    rfl
  · intro sound
    have falseClaim := sound true () (by rfl)
    contradiction

/-- Refusing one distinguished contradiction is weaker than general semantic
soundness. -/
def consistencyOnly : Service Bool Unit where
  run
    | false => .rejected
    | true => .accepted ()

theorem false_refusal_does_not_imply_soundness :
    ¬consistencyOnly.AcceptsSome false ∧
      ¬consistencyOnly.Sound onlyFalseMeaningful := by
  constructor
  · simp [AcceptsSome, Accepts, consistencyOnly]
  · intro sound
    have invalid := sound true () (by rfl)
    contradiction

/-- A small nonvacuous model-sound service: the accepted claim has an
explicit model, while the other claim is model-forbidden. -/
def finiteModelService : Service Bool Unit where
  run
    | false => .accepted ()
    | true => .rejected

def finiteSatisfies (input : Bool) (_ : Unit) (_ : Unit) : Prop :=
  input = false

theorem finiteModelService_modelSound :
    finiteModelService.ModelSound finiteSatisfies := by
  intro input output accepted
  cases input <;> simp [finiteModelService, Accepts] at accepted
  exact ⟨(), rfl⟩

theorem true_is_modelForbidden :
    ModelForbidden finiteSatisfies true := by
  intro output model
  simp [finiteSatisfies]

theorem finiteModelService_refuses_forbidden :
    ¬finiteModelService.AcceptsSome true :=
  finiteModelService_modelSound.not_accepts_forbidden true_is_modelForbidden

def verdicts : List (String × Bool) :=
  [("sound service accepts supported claim",
      decide (soundButIncomplete.run false = .accepted ())),
   ("sound service declines meaningful unsupported claim",
      decide (soundButIncomplete.run true = .declined)),
   ("model-sound service accepts modeled claim",
      decide (finiteModelService.run false = .accepted ())),
   ("model-sound service refuses model-forbidden claim",
      decide (finiteModelService.run true ≠ .accepted ())),
   ("consistency-only service still accepts invalid claim",
      decide (consistencyOnly.run true = .accepted ()))]

end Controls

section AxiomAudit

#print axioms ModelSound.not_accepts_forbidden
#print axioms AcceptanceRefinement.sound
#print axioms AcceptanceRefinement.modelSound
#print axioms AcceptanceRefinement.comp
#print axioms sound_iff_pairChecker_sound
#print axioms ModelSound.pairChecker_sound
#print axioms checkedReconstruction_accepts_iff
#print axioms checkedReconstruction_sound
#print axioms checkedReconstruction_modelSound
#print axioms ofStepDecision_accepts_iff_decide
#print axioms ofStepDecision_accepts_iff
#print axioms catalogHeadService_accepts_iff_ntt
#print axioms Controls.sound_does_not_imply_completeness
#print axioms Controls.agreement_does_not_imply_soundness
#print axioms Controls.false_refusal_does_not_imply_soundness
#print axioms Controls.finiteModelService_refuses_forbidden

end AxiomAudit

end Service

end Mettapedia.Languages.Lean.LeanCheckerAuthorityFlower
