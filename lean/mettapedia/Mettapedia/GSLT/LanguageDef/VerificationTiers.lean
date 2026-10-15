import Mettapedia.GSLT.LanguageDef.ProofSystems

/-!
# Verification tiers

Checkers differ in how much of a derivation the certificate carries and how much the
checker recomputes. `KernelAuthority` has the three standard positions for a theory
whose derivations combine axioms with conversions:

* explicit articles (`explicitChecker`), where every step carries its evidence and the
  checker only compares;
* skeletons (`skeletonChecker`), which keep the shape of the derivation and let decision
  kernels recompute each step;
* decision kernels, which take the empty certificate and compute everything.

This module gives each position its size and its time function and relates them.

* An explicit article is checked in time linear in its size whenever the local checks
  are linear (`explicitTime_le`), so explicit articles over exact linear local checkers
  form a proof system in the sense of Cook and Reckhow (`explicitProofSystem`).
* When the decision kernels are certifying algorithms, built from complete producers
  by `decisionKernelOfProducer`, every accepted skeleton elaborates into an explicit
  article (`skeletonElaboration`). The skeleton checker's run writes that article out
  (`skeleton_traceBounded`), so it does at least the work of reading it
  (`skeleton_work_conservation`). The article is the skeleton plus exactly its
  evidence (`explicitSize_eq`).
* A decision kernel size-simulates every sound checker for its meaning
  (`decisionSizeSimulation`): certificate size alone cannot order the tiers,
  because the empty certificate moves all the work into checking time.

The tiers of the native inference kernel are classes of guest kernels ordered in this
way, by what checking recomputes. MM0's class, whose only conversion is definition
unfolding with explicit evidence, sits at the explicit end.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.VerificationTiers

open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.KernelAuthority.Checker
open Mettapedia.GSLT.LanguageDef.ProofSystems
open Polynomial

universe uClaim uCertificate uJudgment uAxiom uConversion

/-! ## Explicit articles -/

section Explicit

variable {Judgment : Type uJudgment} {AxiomEvidence : Type uAxiom}
  {ConversionEvidence : Type uConversion}

/-- The size of an explicit article: one per node, plus the judgments and evidence it
contains. -/
def explicitSize (judgmentSize : Judgment → ℕ) (axiomSize : AxiomEvidence → ℕ)
    (conversionSize : ConversionEvidence → ℕ) :
    ExplicitCertificate Judgment AxiomEvidence ConversionEvidence → ℕ
  | .base evidence => 1 + axiomSize evidence
  | .convert source prior evidence =>
      1 + judgmentSize source + explicitSize judgmentSize axiomSize conversionSize prior +
        conversionSize evidence

/-- The time function of `checkExplicit`: one unit per call plus the local checks. -/
def explicitTime (axiomTime : Judgment → AxiomEvidence → ℕ)
    (conversionTime : ConversionClaim Judgment → ConversionEvidence → ℕ) :
    Judgment → ExplicitCertificate Judgment AxiomEvidence ConversionEvidence → ℕ
  | target, .base evidence => 1 + axiomTime target evidence
  | target, .convert source prior evidence =>
      1 + explicitTime axiomTime conversionTime source prior +
        conversionTime ⟨source, target⟩ evidence

/-- The total size of the evidence in an explicit article. -/
def evidenceSize (axiomSize : AxiomEvidence → ℕ) (conversionSize : ConversionEvidence → ℕ) :
    ExplicitCertificate Judgment AxiomEvidence ConversionEvidence → ℕ
  | .base evidence => axiomSize evidence
  | .convert _ prior evidence => evidenceSize axiomSize conversionSize prior + conversionSize evidence

/-- The size of a skeleton: one per node, plus the judgments it names. -/
def skeletonSize (judgmentSize : Judgment → ℕ) : KernelSkeleton Judgment → ℕ
  | .base => 1
  | .convert source prior => 1 + judgmentSize source + skeletonSize judgmentSize prior

/-- An explicit article is its skeleton plus exactly its evidence. -/
theorem explicitSize_eq (judgmentSize : Judgment → ℕ) (axiomSize : AxiomEvidence → ℕ)
    (conversionSize : ConversionEvidence → ℕ)
    (article : ExplicitCertificate Judgment AxiomEvidence ConversionEvidence) :
    explicitSize judgmentSize axiomSize conversionSize article =
      skeletonSize judgmentSize article.erase + evidenceSize axiomSize conversionSize article := by
  induction article with
  | base evidence => simp [explicitSize, skeletonSize, evidenceSize, ExplicitCertificate.erase]
  | convert source prior evidence ih =>
      simp only [explicitSize, skeletonSize, evidenceSize, ExplicitCertificate.erase, ih]
      ring

/-- The explicit checker with its sizes and time function. Local claims about a
conversion are measured by the sizes of their two judgments. -/
def explicitTimed (judgmentSize : Judgment → ℕ)
    (axiomChecker : TimedChecker Judgment AxiomEvidence)
    (conversionChecker : TimedChecker (ConversionClaim Judgment) ConversionEvidence) :
    TimedChecker Judgment (ExplicitCertificate Judgment AxiomEvidence ConversionEvidence) where
  toChecker := explicitChecker axiomChecker.toChecker conversionChecker.toChecker
  claimSize := judgmentSize
  certificateSize :=
    explicitSize judgmentSize axiomChecker.certificateSize conversionChecker.certificateSize
  time := explicitTime axiomChecker.time conversionChecker.time

/-- Linear local checks give a linear explicit checker: with local times at most
`a` per unit of input plus `b`, the explicit time is at most `2a + b + 1` per unit of
article plus `a` per unit of the claim. -/
theorem explicitTime_le (judgmentSize : Judgment → ℕ)
    (axiomChecker : TimedChecker Judgment AxiomEvidence)
    (conversionChecker : TimedChecker (ConversionClaim Judgment) ConversionEvidence)
    {a b : ℕ}
    (axiomLinear : ∀ target evidence, axiomChecker.time target evidence ≤
      a * (judgmentSize target + axiomChecker.certificateSize evidence) + b)
    (conversionLinear : ∀ claim evidence, conversionChecker.time claim evidence ≤
      a * (judgmentSize claim.source + judgmentSize claim.target +
        conversionChecker.certificateSize evidence) + b)
    (target : Judgment) (article : ExplicitCertificate Judgment AxiomEvidence ConversionEvidence) :
    explicitTime axiomChecker.time conversionChecker.time target article ≤
      (2 * a + b + 1) *
          explicitSize judgmentSize axiomChecker.certificateSize
            conversionChecker.certificateSize article +
        a * judgmentSize target := by
  induction article generalizing target with
  | base evidence =>
      have local_ := axiomLinear target evidence
      simp only [explicitTime, explicitSize]
      nlinarith
  | convert source prior evidence ih =>
      have previous := ih source
      have local_ := conversionLinear ⟨source, target⟩ evidence
      simp only [explicitTime, explicitSize] at previous local_ ⊢
      nlinarith

/-- The explicit checker runs in linear time when the local checks do. -/
theorem explicitTimed_linearTime (judgmentSize : Judgment → ℕ)
    (axiomChecker : TimedChecker Judgment AxiomEvidence)
    (conversionChecker : TimedChecker (ConversionClaim Judgment) ConversionEvidence)
    {a b : ℕ}
    (axiomLinear : ∀ target evidence, axiomChecker.time target evidence ≤
      a * (judgmentSize target + axiomChecker.certificateSize evidence) + b)
    (conversionLinear : ∀ claim evidence, conversionChecker.time claim evidence ≤
      a * (judgmentSize claim.source + judgmentSize claim.target +
        conversionChecker.certificateSize evidence) + b) :
    (explicitTimed judgmentSize axiomChecker conversionChecker).LinearTime := by
  refine ⟨2 * a + b + 1, 0, fun target article => ?_⟩
  have bound := explicitTime_le judgmentSize axiomChecker conversionChecker axiomLinear
    conversionLinear target article
  simp only [explicitTimed, SizedChecker.inputSize]
  nlinarith

/-- Explicit articles over exact, linear local checkers form a proof system for
derivability in the sense of Cook and Reckhow. -/
def explicitProofSystem {theory : Theory Judgment} (judgmentSize : Judgment → ℕ)
    (axiomChecker : TimedChecker Judgment AxiomEvidence)
    (conversionChecker : TimedChecker (ConversionClaim Judgment) ConversionEvidence)
    (axiomAuthority : axiomChecker.Authority theory.axioms)
    (conversionAuthority : conversionChecker.Authority
      (fun claim => theory.conversion claim.source claim.target))
    {a b : ℕ}
    (axiomLinear : ∀ target evidence, axiomChecker.time target evidence ≤
      a * (judgmentSize target + axiomChecker.certificateSize evidence) + b)
    (conversionLinear : ∀ claim evidence, conversionChecker.time claim evidence ≤
      a * (judgmentSize claim.source + judgmentSize claim.target +
        conversionChecker.certificateSize evidence) + b) :
    ProofSystem Judgment (ExplicitCertificate Judgment AxiomEvidence ConversionEvidence)
      (Derivable theory) where
  toTimedChecker := explicitTimed judgmentSize axiomChecker conversionChecker
  authority := explicitChecker_authority axiomAuthority conversionAuthority
  polynomialTime :=
    (explicitTimed_linearTime judgmentSize axiomChecker conversionChecker axiomLinear
      conversionLinear).polynomialTime

end Explicit

/-! ## Certifying decision kernels -/

section Producers

variable {Claim : Type uClaim} {Certificate : Type uCertificate}

/-- A complete producer whose time function at least writes its output. -/
structure TimedProducer (checker : TimedChecker Claim Certificate) (Meaning : Claim → Prop)
    extends CompleteProducer checker.toChecker Meaning where
  produceTime : Claim → ℕ
  writes : ∀ claim certificate, produce claim = some certificate →
    checker.certificateSize certificate ≤ produceTime claim

/-- The time of the certifying decision kernel: produce, then check what was produced. -/
def TimedProducer.decisionTime {checker : TimedChecker Claim Certificate}
    {Meaning : Claim → Prop} (producer : TimedProducer checker Meaning) (claim : Claim) : ℕ :=
  producer.produceTime claim +
    match producer.produce claim with
    | none => 0
    | some certificate => checker.time claim certificate

theorem TimedProducer.size_le_decisionTime {checker : TimedChecker Claim Certificate}
    {Meaning : Claim → Prop} (producer : TimedProducer checker Meaning) {claim : Claim}
    {certificate : Certificate} (produced : producer.produce claim = some certificate) :
    checker.certificateSize certificate ≤ producer.decisionTime claim :=
  (producer.writes claim certificate produced).trans (Nat.le_add_right _ _)

/-- A decision kernel as a checker of the empty certificate, with its time function. -/
def decisionTimed {Meaning : Claim → Prop} (kernel : DecisionKernel Claim Meaning)
    (claimSize : Claim → ℕ) (decideTime : Claim → ℕ) : TimedChecker Claim Unit where
  toChecker := kernel.toChecker
  claimSize := claimSize
  certificateSize _ := 0
  time claim _ := decideTime claim

/-- A decision kernel size-simulates every sound checker for its meaning: certificate
size orders nothing once the checker computes the whole derivation. -/
def decisionSizeSimulation {Meaning : Claim → Prop} (kernel : DecisionKernel Claim Meaning)
    (claimSize : Claim → ℕ) (decideTime : Claim → ℕ) (checker : SizedChecker Claim Certificate)
    (sound : checker.Sound Meaning) :
    SizeSimulation (decisionTimed kernel claimSize decideTime).toSizedChecker checker where
  translate _ _ := ()
  preserves claim certificate accepted :=
    (kernel.correct claim).mpr (sound claim certificate accepted)
  sizeBound := PolyBoundedBy.const 0 _

/-- A certifying decision kernel elaborates the empty certificate into the evidence its
producer writes. -/
def producerElaboration {checker : TimedChecker Claim Certificate} {Meaning : Claim → Prop}
    (sound : checker.Sound Meaning) (producer : TimedProducer checker Meaning) :
    Elaboration (decisionKernelOfProducer sound producer.toCompleteProducer).toChecker
      checker.toChecker where
  elaborate claim _ := producer.produce claim
  exact claim _ := by
    change checkProduced producer.toCompleteProducer claim = true ↔ _
    unfold checkProduced
    cases produced : producer.produce claim with
    | none => simp
    | some certificate => simp

/-- The certifying decision kernel's run writes its evidence out. -/
theorem producerElaboration_traceBounded {checker : TimedChecker Claim Certificate}
    {Meaning : Claim → Prop} (sound : checker.Sound Meaning) (producer : TimedProducer checker Meaning)
    (claimSize : Claim → ℕ) :
    Elaboration.TraceBounded
      (computing := decisionTimed (decisionKernelOfProducer sound producer.toCompleteProducer)
        claimSize producer.decisionTime)
      (explicit := checker.toSizedChecker) (producerElaboration sound producer) := by
  intro claim _ certificate produced
  exact producer.size_le_decisionTime produced

end Producers

/-! ## Skeletons with certifying kernels -/

section Skeletons

variable {Judgment : Type uJudgment} {AxiomEvidence : Type uAxiom}
  {ConversionEvidence : Type uConversion}

/-- The time function of `checkSkeleton`: one unit per call, the reading of each named
judgment, and the decisions. -/
def skeletonTime (judgmentSize : Judgment → ℕ) (axiomTime : Judgment → ℕ)
    (conversionTime : ConversionClaim Judgment → ℕ) : Judgment → KernelSkeleton Judgment → ℕ
  | target, .base => 1 + axiomTime target
  | target, .convert source prior =>
      1 + judgmentSize source + skeletonTime judgmentSize axiomTime conversionTime source prior +
        conversionTime ⟨source, target⟩

variable {theory : Theory Judgment}
  {axiomChecker : TimedChecker Judgment AxiomEvidence}
  {conversionChecker : TimedChecker (ConversionClaim Judgment) ConversionEvidence}

/-- Elaborate a skeleton by asking the producers for the evidence of each step. -/
def elaborateSkeleton (axiomProducer : TimedProducer axiomChecker theory.axioms)
    (conversionProducer : TimedProducer conversionChecker
      (fun claim => theory.conversion claim.source claim.target)) :
    Judgment → KernelSkeleton Judgment →
      Option (ExplicitCertificate Judgment AxiomEvidence ConversionEvidence)
  | target, .base => (axiomProducer.produce target).map .base
  | target, .convert source prior =>
      match elaborateSkeleton axiomProducer conversionProducer source prior,
          conversionProducer.produce ⟨source, target⟩ with
      | some priorArticle, some evidence => some (.convert source priorArticle evidence)
      | _, _ => none

theorem elaborateSkeleton_convert_eq_some
    (axiomProducer : TimedProducer axiomChecker theory.axioms)
    (conversionProducer : TimedProducer conversionChecker
      (fun claim => theory.conversion claim.source claim.target))
    {target source : Judgment} {prior : KernelSkeleton Judgment}
    {article : ExplicitCertificate Judgment AxiomEvidence ConversionEvidence} :
    elaborateSkeleton axiomProducer conversionProducer target (.convert source prior) = some article ↔
      ∃ priorArticle evidence,
        elaborateSkeleton axiomProducer conversionProducer source prior = some priorArticle ∧
          conversionProducer.produce ⟨source, target⟩ = some evidence ∧
            article = .convert source priorArticle evidence := by
  simp only [elaborateSkeleton]
  cases elaboratedPrior : elaborateSkeleton axiomProducer conversionProducer source prior <;>
    cases produced : conversionProducer.produce ⟨source, target⟩ <;> simp [eq_comm]

/-- The skeleton checker with certifying kernels and its time function. -/
def skeletonTimed (judgmentSize : Judgment → ℕ) (axiomSound : axiomChecker.Sound theory.axioms)
    (conversionSound : conversionChecker.Sound
      (fun claim => theory.conversion claim.source claim.target))
    (axiomProducer : TimedProducer axiomChecker theory.axioms)
    (conversionProducer : TimedProducer conversionChecker
      (fun claim => theory.conversion claim.source claim.target)) :
    TimedChecker Judgment (KernelSkeleton Judgment) where
  toChecker := skeletonChecker (decisionKernelOfProducer axiomSound axiomProducer.toCompleteProducer)
    (decisionKernelOfProducer conversionSound conversionProducer.toCompleteProducer)
  claimSize := judgmentSize
  certificateSize := skeletonSize judgmentSize
  time := skeletonTime judgmentSize axiomProducer.decisionTime conversionProducer.decisionTime

/-- A skeleton is accepted exactly when its elaboration exists and the explicit checker
accepts it. -/
theorem checkSkeleton_iff_elaborated (axiomSound : axiomChecker.Sound theory.axioms)
    (conversionSound : conversionChecker.Sound
      (fun claim => theory.conversion claim.source claim.target))
    (axiomProducer : TimedProducer axiomChecker theory.axioms)
    (conversionProducer : TimedProducer conversionChecker
      (fun claim => theory.conversion claim.source claim.target))
    (target : Judgment) (skeleton : KernelSkeleton Judgment) :
    checkSkeleton (decisionKernelOfProducer axiomSound axiomProducer.toCompleteProducer)
        (decisionKernelOfProducer conversionSound conversionProducer.toCompleteProducer)
        target skeleton = true ↔
      ∃ article, elaborateSkeleton axiomProducer conversionProducer target skeleton = some article ∧
        checkExplicit axiomChecker.toChecker conversionChecker.toChecker target article = true := by
  induction skeleton generalizing target with
  | base =>
      rw [checkSkeleton]
      change checkProduced axiomProducer.toCompleteProducer target = true ↔ _
      simp only [checkProduced, elaborateSkeleton]
      cases produced : axiomProducer.produce target with
      | none => simp
      | some evidence => simp [checkExplicit]
  | convert source prior ih =>
      rw [checkSkeleton, Bool.and_eq_true, ih]
      change (_ ∧ checkProduced conversionProducer.toCompleteProducer ⟨source, target⟩ = true) ↔ _
      constructor
      · rintro ⟨⟨priorArticle, elaborated, accepted⟩, decided⟩
        unfold checkProduced at decided
        cases produced : conversionProducer.produce ⟨source, target⟩ with
        | none => simp [produced] at decided
        | some evidence =>
            simp only [produced] at decided
            exact ⟨.convert source priorArticle evidence,
              (elaborateSkeleton_convert_eq_some axiomProducer conversionProducer).mpr
                ⟨priorArticle, evidence, elaborated, produced, rfl⟩,
              by rw [checkExplicit, accepted, decided]; rfl⟩
      · rintro ⟨article, elaborated, accepted⟩
        obtain ⟨priorArticle, evidence, elaboratedPrior, produced, rfl⟩ :=
          (elaborateSkeleton_convert_eq_some axiomProducer conversionProducer).mp elaborated
        rw [checkExplicit, Bool.and_eq_true] at accepted
        refine ⟨⟨priorArticle, elaboratedPrior, accepted.1⟩, ?_⟩
        unfold checkProduced
        rw [produced]
        exact accepted.2

/-- Skeletons with certifying kernels elaborate into explicit articles. -/
def skeletonElaboration (judgmentSize : Judgment → ℕ)
    (axiomSound : axiomChecker.Sound theory.axioms)
    (conversionSound : conversionChecker.Sound
      (fun claim => theory.conversion claim.source claim.target))
    (axiomProducer : TimedProducer axiomChecker theory.axioms)
    (conversionProducer : TimedProducer conversionChecker
      (fun claim => theory.conversion claim.source claim.target)) :
    Elaboration
      (skeletonTimed judgmentSize axiomSound conversionSound axiomProducer conversionProducer).toChecker
      (explicitTimed judgmentSize axiomChecker conversionChecker).toChecker where
  elaborate := elaborateSkeleton axiomProducer conversionProducer
  exact := checkSkeleton_iff_elaborated axiomSound conversionSound axiomProducer conversionProducer

/-- The elaborated article keeps the skeleton it came from. -/
theorem elaborateSkeleton_erase
    (axiomProducer : TimedProducer axiomChecker theory.axioms)
    (conversionProducer : TimedProducer conversionChecker
      (fun claim => theory.conversion claim.source claim.target))
    {target : Judgment} {skeleton : KernelSkeleton Judgment}
    {article : ExplicitCertificate Judgment AxiomEvidence ConversionEvidence}
    (elaborated : elaborateSkeleton axiomProducer conversionProducer target skeleton = some article) :
    article.erase = skeleton := by
  induction skeleton generalizing target article with
  | base =>
      simp only [elaborateSkeleton] at elaborated
      cases produced : axiomProducer.produce target with
      | none => simp [produced] at elaborated
      | some evidence =>
          simp only [produced, Option.map_some, Option.some.injEq] at elaborated
          subst elaborated
          rfl
  | convert source prior ih =>
      obtain ⟨priorArticle, evidence, elaboratedPrior, _, rfl⟩ :=
        (elaborateSkeleton_convert_eq_some axiomProducer conversionProducer).mp elaborated
      simp [ExplicitCertificate.erase, ih elaboratedPrior]

/-- The skeleton checker's run writes the elaborated article out. -/
theorem skeleton_traceBounded (judgmentSize : Judgment → ℕ)
    (axiomSound : axiomChecker.Sound theory.axioms)
    (conversionSound : conversionChecker.Sound
      (fun claim => theory.conversion claim.source claim.target))
    (axiomProducer : TimedProducer axiomChecker theory.axioms)
    (conversionProducer : TimedProducer conversionChecker
      (fun claim => theory.conversion claim.source claim.target)) :
    (skeletonElaboration judgmentSize axiomSound conversionSound axiomProducer
      conversionProducer).TraceBounded
      (computing := skeletonTimed judgmentSize axiomSound conversionSound axiomProducer
        conversionProducer)
      (explicit := (explicitTimed judgmentSize axiomChecker conversionChecker).toSizedChecker) := by
  intro target skeleton article elaborated
  change elaborateSkeleton axiomProducer conversionProducer target skeleton = some article
    at elaborated
  change explicitSize judgmentSize axiomChecker.certificateSize conversionChecker.certificateSize
      article ≤ skeletonTime judgmentSize axiomProducer.decisionTime conversionProducer.decisionTime
      target skeleton
  induction skeleton generalizing target article with
  | base =>
      simp only [elaborateSkeleton] at elaborated
      cases produced : axiomProducer.produce target with
      | none => simp [produced] at elaborated
      | some evidence =>
          simp only [produced, Option.map_some, Option.some.injEq] at elaborated
          subst elaborated
          simp only [explicitSize, skeletonTime]
          exact Nat.add_le_add_left (axiomProducer.size_le_decisionTime produced) 1
  | convert source prior ih =>
      obtain ⟨priorArticle, evidence, elaboratedPrior, produced, rfl⟩ :=
        (elaborateSkeleton_convert_eq_some axiomProducer conversionProducer).mp elaborated
      have previous := ih source priorArticle elaboratedPrior
      have local_ := conversionProducer.size_le_decisionTime produced
      simp only [explicitSize, skeletonTime]
      omega

/-- Work conservation for skeletons: an accepted skeleton costs its checker at least the
size of an explicit article that the explicit checker accepts. -/
theorem skeleton_work_conservation (judgmentSize : Judgment → ℕ)
    (axiomSound : axiomChecker.Sound theory.axioms)
    (conversionSound : conversionChecker.Sound
      (fun claim => theory.conversion claim.source claim.target))
    (axiomProducer : TimedProducer axiomChecker theory.axioms)
    (conversionProducer : TimedProducer conversionChecker
      (fun claim => theory.conversion claim.source claim.target))
    {target : Judgment} {skeleton : KernelSkeleton Judgment}
    (accepted : (skeletonTimed judgmentSize axiomSound conversionSound axiomProducer
      conversionProducer).check target skeleton = true) :
    ∃ article, (explicitChecker axiomChecker.toChecker conversionChecker.toChecker).check
        target article = true ∧
      explicitSize judgmentSize axiomChecker.certificateSize conversionChecker.certificateSize
          article ≤
        skeletonTime judgmentSize axiomProducer.decisionTime conversionProducer.decisionTime
          target skeleton :=
  (skeletonElaboration judgmentSize axiomSound conversionSound axiomProducer
    conversionProducer).work_conservation
    (skeleton_traceBounded judgmentSize axiomSound conversionSound axiomProducer
      conversionProducer) accepted

end Skeletons

/-! ## Controls -/

namespace Controls

/-- Judgments are numbers; the axiom is `0` and each conversion adds one. The evidence
for the axiom is empty, and the evidence for a conversion is the difference it adds. -/
def theory : Theory ℕ where
  axioms judgment := judgment = 0
  conversion source target := target = source + 1

def axiomChecker : TimedChecker ℕ Unit where
  check judgment _ := decide (judgment = 0)
  claimSize := Nat.size
  certificateSize _ := 0
  time judgment _ := judgment.size + 1

def conversionChecker : TimedChecker (ConversionClaim ℕ) ℕ where
  check claim difference := decide (difference = 1 ∧ claim.target = claim.source + difference)
  claimSize claim := claim.source.size + claim.target.size
  certificateSize difference := difference.size
  time claim difference := claim.source.size + claim.target.size + difference.size + 1

theorem axiomChecker_authority : axiomChecker.Authority theory.axioms where
  sound judgment _ accepted := by simpa [axiomChecker, theory] using accepted
  complete judgment isAxiom := ⟨(), by simpa [axiomChecker, theory] using isAxiom⟩

theorem conversionChecker_authority :
    conversionChecker.Authority (fun claim => theory.conversion claim.source claim.target) where
  sound claim difference accepted := by
    simp only [conversionChecker, decide_eq_true_eq] at accepted
    simp [theory, accepted.2, accepted.1]
  complete claim converts := ⟨1, by simpa [conversionChecker, theory] using converts⟩

/-- Explicit articles for the successor theory form a linear-time proof system. -/
def successorSystem : ProofSystem ℕ (ExplicitCertificate ℕ Unit ℕ) (Derivable theory) :=
  explicitProofSystem Nat.size axiomChecker conversionChecker axiomChecker_authority
    conversionChecker_authority (a := 1) (b := 1)
    (fun judgment _ => by simp only [axiomChecker]; omega)
    (fun claim difference => by simp only [conversionChecker]; omega)

/-- The article for `2`: the axiom, then two conversions. -/
def two : ExplicitCertificate ℕ Unit ℕ := .convert 1 (.convert 0 (.base ()) 1) 1

example : successorSystem.check 2 two = true := by
  simp [successorSystem, explicitProofSystem, explicitTimed, explicitChecker, checkExplicit, two,
    axiomChecker, conversionChecker]

/-- The same article does not prove `3`. -/
example : successorSystem.check 3 two = false := by
  simp [successorSystem, explicitProofSystem, explicitTimed, explicitChecker, checkExplicit, two,
    axiomChecker, conversionChecker]

/-- Erasing the evidence of the article leaves its skeleton, and the sizes differ by
exactly the evidence. -/
example : two.erase = .convert 1 (.convert 0 .base) := rfl

example : explicitSize Nat.size (fun _ => 0) Nat.size two =
    skeletonSize Nat.size two.erase + evidenceSize (fun _ => 0) Nat.size two :=
  explicitSize_eq _ _ _ _

end Controls

end Mettapedia.GSLT.LanguageDef.VerificationTiers
