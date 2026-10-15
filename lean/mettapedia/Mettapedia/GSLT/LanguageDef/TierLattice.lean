import Mettapedia.GSLT.LanguageDef.VerificationTiers
import Mettapedia.OSLF.Framework.GSLTTypeSynthesis

/-!
# The tier lattice

A theory whose derivations combine axioms and conversions can be checked at several
tiers. A tier fixes, for each kind of step, a local checker and the evidence it reads
(`Tier`). Its certificates are explicit articles over that evidence (`Tier.checker`).
The lowest tier reads full evidence for every step and only compares; a higher tier
reads less evidence and recomputes more; the highest tier reads none and decides every
step, so its articles are skeletons.

One tier lies above another when each of its local checkers elaborates into the
other's (`Above`).

* The local elaborations lift to the articles node by node (`liftElaboration`). The
  lift of a composite is the composite of the lifts (`liftArticle_compose`), so the
  tiers form a preorder on which elaboration acts functorially (`Above.refl`,
  `Above.trans`).
* Soundness passes from a lower tier to every tier above it without trusting any
  producer (`Above.sound`).
* The lower article is the upper article's skeleton plus the evidence written in
  (`liftArticle_size`). When each local elaboration writes within its local time, the
  lower article is at most that skeleton plus the upper tier's checking time
  (`liftArticle_work`): reading less evidence means computing more.
* The lowest tier checks in linear time when its local checks do
  (`VerificationTiers.explicitTime_le`), and a kernel that decides whole claims
  size-simulates every sound checker (`VerificationTiers.decisionSizeSimulation`).

Above a checker stands only what elaborates into it, and two kinds of checkers do not.
An unsound tier lies above no sound tier (`not_above_of_unsound`). A checker charged
less time than every explicit certificate it would need has no elaboration that writes
within its time (`not_traceBounded_of_fast`). The second is the position of a trusted
native kernel: correct, perhaps, but its correctness is taken on trust.

The same picture holds in operational logical form. Coarsening a GSLT so that one step
is a nonempty path of its steps (`coarsen`) keeps reachability, so every native type
defined by reaching a goal is unchanged (`coarsen_multiStep_iff`). It turns the
multi-step modalities into one-step ones (`coarsen_diamond_iff`). Each coarse step
stands for at least one step underneath, and any nonempty path is a single coarse
step (`coarse_stepsIn_load`, `coarse_step_of_stepsIn`). That count of steps underneath
is the computational load that the higher tier recomputes.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TierLattice

open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.KernelAuthority.Checker
open Mettapedia.GSLT.LanguageDef.ProofSystems
open Mettapedia.GSLT.LanguageDef.VerificationTiers

universe uClaim uCertificate uMiddle uExplicit uJudgment
  uUpperAxiom uUpperConversion uMiddleAxiom uMiddleConversion uLowerAxiom uLowerConversion

/-! ## Elaborations compose -/

section Compose

variable {Claim : Type uClaim} {Certificate : Type uCertificate} {Middle : Type uMiddle}
  {Explicit : Type uExplicit}

/-- The identity elaboration. -/
def _root_.Mettapedia.GSLT.LanguageDef.ProofSystems.Elaboration.identity
    (checker : Checker Claim Certificate) : Elaboration checker checker where
  elaborate _ certificate := some certificate
  exact claim certificate := by simp

/-- Elaborate into an intermediate checker, then elaborate its certificate further. -/
def _root_.Mettapedia.GSLT.LanguageDef.ProofSystems.Elaboration.compose
    {upper : Checker Claim Certificate} {middle : Checker Claim Middle}
    {lower : Checker Claim Explicit} (first : Elaboration upper middle)
    (second : Elaboration middle lower) : Elaboration upper lower where
  elaborate claim certificate := (first.elaborate claim certificate).bind (second.elaborate claim)
  exact claim certificate := by
    rw [first.exact]
    constructor
    · rintro ⟨intermediate, produced, accepted⟩
      obtain ⟨elaborated, producedFurther, acceptedFurther⟩ :=
        (second.exact claim intermediate).mp accepted
      exact ⟨elaborated, by simp [produced, producedFurther], acceptedFurther⟩
    · rintro ⟨elaborated, produced, accepted⟩
      cases producedFirst : first.elaborate claim certificate with
      | none => simp [producedFirst] at produced
      | some intermediate =>
          simp only [producedFirst, Option.bind_some] at produced
          exact ⟨intermediate, rfl, (second.exact claim intermediate).mpr
            ⟨elaborated, produced, accepted⟩⟩

end Compose

/-! ## Lifting local elaborations to articles -/

section Lift

variable {Judgment : Type uJudgment}
  {UpperAxiom : Type uUpperAxiom} {UpperConversion : Type uUpperConversion}
  {MiddleAxiom : Type uMiddleAxiom} {MiddleConversion : Type uMiddleConversion}
  {LowerAxiom : Type uLowerAxiom} {LowerConversion : Type uLowerConversion}

/-- Elaborate an article node by node with local elaborators. -/
def liftArticle
    (axiomElaborate : Judgment → UpperAxiom → Option LowerAxiom)
    (conversionElaborate : ConversionClaim Judgment → UpperConversion → Option LowerConversion) :
    Judgment → ExplicitCertificate Judgment UpperAxiom UpperConversion →
      Option (ExplicitCertificate Judgment LowerAxiom LowerConversion)
  | target, .base evidence => (axiomElaborate target evidence).map .base
  | target, .convert source prior evidence =>
      match liftArticle axiomElaborate conversionElaborate source prior,
          conversionElaborate ⟨source, target⟩ evidence with
      | some priorArticle, some lowered => some (.convert source priorArticle lowered)
      | _, _ => none

theorem liftArticle_base_eq_some
    {axiomElaborate : Judgment → UpperAxiom → Option LowerAxiom}
    {conversionElaborate : ConversionClaim Judgment → UpperConversion → Option LowerConversion}
    {target : Judgment} {evidence : UpperAxiom}
    {article : ExplicitCertificate Judgment LowerAxiom LowerConversion} :
    liftArticle axiomElaborate conversionElaborate target (.base evidence) = some article ↔
      ∃ lowered, axiomElaborate target evidence = some lowered ∧ article = .base lowered := by
  simp only [liftArticle, Option.map_eq_some_iff]
  constructor
  · rintro ⟨lowered, produced, rfl⟩
    exact ⟨lowered, produced, rfl⟩
  · rintro ⟨lowered, produced, rfl⟩
    exact ⟨lowered, produced, rfl⟩

theorem liftArticle_convert_eq_some
    {axiomElaborate : Judgment → UpperAxiom → Option LowerAxiom}
    {conversionElaborate : ConversionClaim Judgment → UpperConversion → Option LowerConversion}
    {target source : Judgment} {prior : ExplicitCertificate Judgment UpperAxiom UpperConversion}
    {evidence : UpperConversion}
    {article : ExplicitCertificate Judgment LowerAxiom LowerConversion} :
    liftArticle axiomElaborate conversionElaborate target (.convert source prior evidence) =
        some article ↔
      ∃ priorArticle lowered,
        liftArticle axiomElaborate conversionElaborate source prior = some priorArticle ∧
          conversionElaborate ⟨source, target⟩ evidence = some lowered ∧
            article = .convert source priorArticle lowered := by
  simp only [liftArticle]
  cases liftedPrior : liftArticle axiomElaborate conversionElaborate source prior <;>
    cases lowered : conversionElaborate ⟨source, target⟩ evidence <;> simp [eq_comm]

/-- Local elaborations lift to an elaboration of articles. -/
def liftElaboration
    {upperAxiomChecker : Checker Judgment UpperAxiom}
    {upperConversionChecker : Checker (ConversionClaim Judgment) UpperConversion}
    {lowerAxiomChecker : Checker Judgment LowerAxiom}
    {lowerConversionChecker : Checker (ConversionClaim Judgment) LowerConversion}
    (axiomElaboration : Elaboration upperAxiomChecker lowerAxiomChecker)
    (conversionElaboration : Elaboration upperConversionChecker lowerConversionChecker) :
    Elaboration (explicitChecker upperAxiomChecker upperConversionChecker)
      (explicitChecker lowerAxiomChecker lowerConversionChecker) where
  elaborate := liftArticle axiomElaboration.elaborate conversionElaboration.elaborate
  exact target article := by
    change checkExplicit upperAxiomChecker upperConversionChecker target article = true ↔
      ∃ lowered, liftArticle axiomElaboration.elaborate conversionElaboration.elaborate target
          article = some lowered ∧
        checkExplicit lowerAxiomChecker lowerConversionChecker target lowered = true
    induction article generalizing target with
    | base evidence =>
        rw [checkExplicit, axiomElaboration.exact]
        constructor
        · rintro ⟨lowered, produced, accepted⟩
          exact ⟨.base lowered, liftArticle_base_eq_some.mpr ⟨lowered, produced, rfl⟩,
            by rw [checkExplicit]; exact accepted⟩
        · rintro ⟨article, lifted, accepted⟩
          obtain ⟨lowered, produced, rfl⟩ := liftArticle_base_eq_some.mp lifted
          rw [checkExplicit] at accepted
          exact ⟨lowered, produced, accepted⟩
    | convert source prior evidence ih =>
        rw [checkExplicit, Bool.and_eq_true, ih, conversionElaboration.exact]
        constructor
        · rintro ⟨⟨priorArticle, liftedPrior, acceptedPrior⟩, ⟨lowered, produced, accepted⟩⟩
          exact ⟨.convert source priorArticle lowered,
            liftArticle_convert_eq_some.mpr ⟨priorArticle, lowered, liftedPrior, produced, rfl⟩,
            by rw [checkExplicit, acceptedPrior, accepted]; rfl⟩
        · rintro ⟨article, lifted, accepted⟩
          obtain ⟨priorArticle, lowered, liftedPrior, produced, rfl⟩ :=
            liftArticle_convert_eq_some.mp lifted
          rw [checkExplicit, Bool.and_eq_true] at accepted
          exact ⟨⟨priorArticle, liftedPrior, accepted.1⟩, ⟨lowered, produced, accepted.2⟩⟩

/-- Lifting keeps the skeleton: only evidence changes. -/
theorem liftArticle_erase
    {axiomElaborate : Judgment → UpperAxiom → Option LowerAxiom}
    {conversionElaborate : ConversionClaim Judgment → UpperConversion → Option LowerConversion}
    {target : Judgment} {article : ExplicitCertificate Judgment UpperAxiom UpperConversion}
    {lowered : ExplicitCertificate Judgment LowerAxiom LowerConversion}
    (lifted : liftArticle axiomElaborate conversionElaborate target article = some lowered) :
    lowered.erase = article.erase := by
  induction article generalizing target lowered with
  | base evidence =>
      obtain ⟨_, _, rfl⟩ := liftArticle_base_eq_some.mp lifted
      rfl
  | convert source prior evidence ih =>
      obtain ⟨priorArticle, _, liftedPrior, _, rfl⟩ := liftArticle_convert_eq_some.mp lifted
      simp [ExplicitCertificate.erase, ih liftedPrior]

/-- Lifting along a composite of local elaborators is lifting twice. -/
theorem liftArticle_compose
    (axiomFirst : Judgment → UpperAxiom → Option MiddleAxiom)
    (conversionFirst : ConversionClaim Judgment → UpperConversion → Option MiddleConversion)
    (axiomSecond : Judgment → MiddleAxiom → Option LowerAxiom)
    (conversionSecond : ConversionClaim Judgment → MiddleConversion → Option LowerConversion)
    (target : Judgment) (article : ExplicitCertificate Judgment UpperAxiom UpperConversion) :
    liftArticle (fun claim evidence => (axiomFirst claim evidence).bind (axiomSecond claim))
        (fun claim evidence => (conversionFirst claim evidence).bind (conversionSecond claim))
        target article =
      (liftArticle axiomFirst conversionFirst target article).bind
        (liftArticle axiomSecond conversionSecond target) := by
  induction article generalizing target with
  | base evidence =>
      simp only [liftArticle]
      cases axiomFirst target evidence <;> simp [liftArticle]
  | convert source prior evidence ih =>
      simp only [liftArticle, ih]
      cases liftArticle axiomFirst conversionFirst source prior with
      | none => simp
      | some middleArticle =>
          cases conversionFirst ⟨source, target⟩ evidence with
          | none =>
              simp only [Option.bind_some, Option.bind_none]
              cases liftArticle axiomSecond conversionSecond source middleArticle <;> simp
          | some middleEvidence =>
              simp only [Option.bind_some, liftArticle]

/-- The size of a lifted article is the original skeleton plus the evidence written in. -/
theorem liftArticle_size (judgmentSize : Judgment → ℕ) (axiomSize : LowerAxiom → ℕ)
    (conversionSize : LowerConversion → ℕ)
    {axiomElaborate : Judgment → UpperAxiom → Option LowerAxiom}
    {conversionElaborate : ConversionClaim Judgment → UpperConversion → Option LowerConversion}
    {target : Judgment} {article : ExplicitCertificate Judgment UpperAxiom UpperConversion}
    {lowered : ExplicitCertificate Judgment LowerAxiom LowerConversion}
    (lifted : liftArticle axiomElaborate conversionElaborate target article = some lowered) :
    explicitSize judgmentSize axiomSize conversionSize lowered =
      skeletonSize judgmentSize article.erase + evidenceSize axiomSize conversionSize lowered := by
  rw [explicitSize_eq, liftArticle_erase lifted]

/-- When each local elaborator writes within its local time, the evidence written into a
lifted article is at most the upper article's checking time. -/
theorem liftArticle_evidence_le (axiomSize : LowerAxiom → ℕ)
    (conversionSize : LowerConversion → ℕ)
    (axiomTime : Judgment → UpperAxiom → ℕ)
    (conversionTime : ConversionClaim Judgment → UpperConversion → ℕ)
    {axiomElaborate : Judgment → UpperAxiom → Option LowerAxiom}
    {conversionElaborate : ConversionClaim Judgment → UpperConversion → Option LowerConversion}
    (axiomWrites : ∀ target evidence lowered, axiomElaborate target evidence = some lowered →
      axiomSize lowered ≤ axiomTime target evidence)
    (conversionWrites : ∀ claim evidence lowered,
      conversionElaborate claim evidence = some lowered →
        conversionSize lowered ≤ conversionTime claim evidence)
    {target : Judgment} {article : ExplicitCertificate Judgment UpperAxiom UpperConversion}
    {lowered : ExplicitCertificate Judgment LowerAxiom LowerConversion}
    (lifted : liftArticle axiomElaborate conversionElaborate target article = some lowered) :
    evidenceSize axiomSize conversionSize lowered ≤
      explicitTime axiomTime conversionTime target article := by
  induction article generalizing target lowered with
  | base evidence =>
      obtain ⟨loweredEvidence, produced, rfl⟩ := liftArticle_base_eq_some.mp lifted
      have local_ := axiomWrites target evidence loweredEvidence produced
      simp only [evidenceSize, explicitTime]
      omega
  | convert source prior evidence ih =>
      obtain ⟨priorArticle, loweredEvidence, liftedPrior, produced, rfl⟩ :=
        liftArticle_convert_eq_some.mp lifted
      have previous := ih liftedPrior
      have local_ := conversionWrites ⟨source, target⟩ evidence loweredEvidence produced
      simp only [evidenceSize, explicitTime]
      omega

/-- Work on an edge of the lattice: the lower article is at most the upper article's
skeleton plus the upper tier's checking time. -/
theorem liftArticle_work (judgmentSize : Judgment → ℕ) (axiomSize : LowerAxiom → ℕ)
    (conversionSize : LowerConversion → ℕ)
    (axiomTime : Judgment → UpperAxiom → ℕ)
    (conversionTime : ConversionClaim Judgment → UpperConversion → ℕ)
    {axiomElaborate : Judgment → UpperAxiom → Option LowerAxiom}
    {conversionElaborate : ConversionClaim Judgment → UpperConversion → Option LowerConversion}
    (axiomWrites : ∀ target evidence lowered, axiomElaborate target evidence = some lowered →
      axiomSize lowered ≤ axiomTime target evidence)
    (conversionWrites : ∀ claim evidence lowered,
      conversionElaborate claim evidence = some lowered →
        conversionSize lowered ≤ conversionTime claim evidence)
    {target : Judgment} {article : ExplicitCertificate Judgment UpperAxiom UpperConversion}
    {lowered : ExplicitCertificate Judgment LowerAxiom LowerConversion}
    (lifted : liftArticle axiomElaborate conversionElaborate target article = some lowered) :
    explicitSize judgmentSize axiomSize conversionSize lowered ≤
      skeletonSize judgmentSize article.erase + explicitTime axiomTime conversionTime target article := by
  rw [liftArticle_size judgmentSize axiomSize conversionSize lifted]
  exact Nat.add_le_add_left
    (liftArticle_evidence_le axiomSize conversionSize axiomTime conversionTime axiomWrites
      conversionWrites lifted) _

end Lift

/-! ## Tiers -/

section Tiers

variable {Judgment : Type uJudgment}

/-- A tier: a local checker for axioms and one for conversions, with the evidence each
reads. -/
structure Tier (Judgment : Type uJudgment) (AxiomEvidence : Type uUpperAxiom)
    (ConversionEvidence : Type uUpperConversion) where
  axiomChecker : TimedChecker Judgment AxiomEvidence
  conversionChecker : TimedChecker (ConversionClaim Judgment) ConversionEvidence

variable {UpperAxiom : Type uUpperAxiom} {UpperConversion : Type uUpperConversion}
  {MiddleAxiom : Type uMiddleAxiom} {MiddleConversion : Type uMiddleConversion}
  {LowerAxiom : Type uLowerAxiom} {LowerConversion : Type uLowerConversion}

namespace Tier

/-- The checker of a tier's articles. -/
def checker (judgmentSize : Judgment → ℕ) (tier : Tier Judgment UpperAxiom UpperConversion) :
    TimedChecker Judgment (ExplicitCertificate Judgment UpperAxiom UpperConversion) :=
  explicitTimed judgmentSize tier.axiomChecker tier.conversionChecker

/-- Each local checker is sound for its kind of step. -/
def LocallySound (theory : Theory Judgment) (tier : Tier Judgment UpperAxiom UpperConversion) :
    Prop :=
  tier.axiomChecker.Sound theory.axioms ∧
    tier.conversionChecker.Sound (fun claim => theory.conversion claim.source claim.target)

/-- A locally sound tier's articles prove only derivable judgments. -/
theorem checker_sound {theory : Theory Judgment} (judgmentSize : Judgment → ℕ)
    {tier : Tier Judgment UpperAxiom UpperConversion} (sound : tier.LocallySound theory) :
    (tier.checker judgmentSize).Sound (Derivable theory) :=
  fun _ _ accepted => checkExplicit_sound sound.1 sound.2 accepted

end Tier

/-- One tier lies above another when each of its local checkers elaborates into the
other's. -/
structure Above (upper : Tier Judgment UpperAxiom UpperConversion)
    (lower : Tier Judgment LowerAxiom LowerConversion) where
  axiomElaboration : Elaboration upper.axiomChecker.toChecker lower.axiomChecker.toChecker
  conversionElaboration :
    Elaboration upper.conversionChecker.toChecker lower.conversionChecker.toChecker

namespace Above

/-- Every tier lies above itself. -/
def refl (tier : Tier Judgment UpperAxiom UpperConversion) : Above tier tier where
  axiomElaboration := Elaboration.identity _
  conversionElaboration := Elaboration.identity _

/-- Lying above is transitive. -/
def trans {upper : Tier Judgment UpperAxiom UpperConversion}
    {middle : Tier Judgment MiddleAxiom MiddleConversion}
    {lower : Tier Judgment LowerAxiom LowerConversion}
    (first : Above upper middle) (second : Above middle lower) : Above upper lower where
  axiomElaboration := first.axiomElaboration.compose second.axiomElaboration
  conversionElaboration := first.conversionElaboration.compose second.conversionElaboration

/-- The elaboration of articles from the upper tier into the lower one. -/
def elaboration {upper : Tier Judgment UpperAxiom UpperConversion}
    {lower : Tier Judgment LowerAxiom LowerConversion} (above : Above upper lower)
    (judgmentSize : Judgment → ℕ) :
    Elaboration (upper.checker judgmentSize).toChecker (lower.checker judgmentSize).toChecker :=
  liftElaboration above.axiomElaboration above.conversionElaboration

/-- Functoriality: elaborating through a middle tier is elaborating directly. -/
theorem elaboration_trans {upper : Tier Judgment UpperAxiom UpperConversion}
    {middle : Tier Judgment MiddleAxiom MiddleConversion}
    {lower : Tier Judgment LowerAxiom LowerConversion}
    (first : Above upper middle) (second : Above middle lower) (judgmentSize : Judgment → ℕ)
    (target : Judgment) (article : ExplicitCertificate Judgment UpperAxiom UpperConversion) :
    ((first.trans second).elaboration judgmentSize).elaborate target article =
      ((first.elaboration judgmentSize).compose (second.elaboration judgmentSize)).elaborate
        target article :=
  liftArticle_compose _ _ _ _ target article

/-- Soundness passes up: a tier above a locally sound tier is locally sound, with no
trust in the elaborators. -/
theorem sound {theory : Theory Judgment} {upper : Tier Judgment UpperAxiom UpperConversion}
    {lower : Tier Judgment LowerAxiom LowerConversion} (above : Above upper lower)
    (lowerSound : lower.LocallySound theory) : upper.LocallySound theory :=
  ⟨above.axiomElaboration.sound lowerSound.1, above.conversionElaboration.sound lowerSound.2⟩

/-- The local elaborations write within the upper tier's local times. -/
def Writes {upper : Tier Judgment UpperAxiom UpperConversion}
    {lower : Tier Judgment LowerAxiom LowerConversion} (above : Above upper lower) : Prop :=
  (∀ target evidence lowered, above.axiomElaboration.elaborate target evidence = some lowered →
      lower.axiomChecker.certificateSize lowered ≤ upper.axiomChecker.time target evidence) ∧
    (∀ claim evidence lowered,
      above.conversionElaboration.elaborate claim evidence = some lowered →
        lower.conversionChecker.certificateSize lowered ≤ upper.conversionChecker.time claim evidence)

/-- Work on an edge: when the elaborations write within their local times, every
elaborated article is at most the upper skeleton plus the upper checking time. -/
theorem work {upper : Tier Judgment UpperAxiom UpperConversion}
    {lower : Tier Judgment LowerAxiom LowerConversion} (above : Above upper lower)
    (writes : above.Writes) (judgmentSize : Judgment → ℕ) {target : Judgment}
    {article : ExplicitCertificate Judgment UpperAxiom UpperConversion}
    {lowered : ExplicitCertificate Judgment LowerAxiom LowerConversion}
    (elaborated : (above.elaboration judgmentSize).elaborate target article = some lowered) :
    (lower.checker judgmentSize).certificateSize lowered ≤
      skeletonSize judgmentSize article.erase + (upper.checker judgmentSize).time target article :=
  liftArticle_work judgmentSize lower.axiomChecker.certificateSize
    lower.conversionChecker.certificateSize upper.axiomChecker.time upper.conversionChecker.time
    writes.1 writes.2 elaborated

end Above

/-- An unsound tier lies above no locally sound tier. -/
theorem not_above_of_unsound {theory : Theory Judgment}
    {upper : Tier Judgment UpperAxiom UpperConversion}
    {lower : Tier Judgment LowerAxiom LowerConversion}
    (unsound : ¬ upper.LocallySound theory) (lowerSound : lower.LocallySound theory) :
    ¬ Nonempty (Above upper lower) :=
  fun ⟨above⟩ => unsound (above.sound lowerSound)

end Tiers

/-- A checker charged less time than every explicit certificate it would need has no
elaboration that writes within its time. -/
theorem not_traceBounded_of_fast {Claim : Type uClaim} {Certificate : Type uCertificate}
    {Explicit : Type uExplicit} {computing : TimedChecker Claim Certificate}
    {explicit : SizedChecker Claim Explicit}
    (elaboration : Elaboration computing.toChecker explicit.toChecker) {claim : Claim}
    {certificate : Certificate} (accepted : computing.check claim certificate = true)
    (fast : ∀ elaborated, explicit.check claim elaborated = true →
      computing.time claim certificate < explicit.certificateSize elaborated) :
    ¬ elaboration.TraceBounded := by
  intro traced
  obtain ⟨elaborated, explicitAccepted, small⟩ := elaboration.work_conservation traced accepted
  exact absurd small (Nat.not_le.mpr (fast elaborated explicitAccepted))

/-! ## Coarsening in operational logical form -/

section Coarsening

open Mettapedia.GSLT
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

universe uTerm

/-- The coarsening of a GSLT: one step is a nonempty path of its steps. -/
def coarsen (theory : GSLT.{uTerm}) : GSLT.{uTerm} where
  Term := theory.Term
  equations := theory.equations
  rewrites := Relation.TransGen theory.rewrites
  rewrites_resp_left := by
    intro t t' u equivalent path
    induction path with
    | single step =>
        obtain ⟨u', step', related⟩ := theory.rewrites_resp_left equivalent step
        exact ⟨u', .single step', related⟩
    | tail _ step ih =>
        obtain ⟨middle', path', related⟩ := ih
        obtain ⟨u', step', related'⟩ := theory.rewrites_resp_left related step
        exact ⟨u', path'.tail step', related'⟩
  rewrites_resp_right := by
    intro t u u' path equivalent
    cases path with
    | single step => exact .single (theory.rewrites_resp_right step equivalent)
    | tail path step => exact path.tail (theory.rewrites_resp_right step equivalent)

theorem coarsen_step_iff (theory : GSLT.{uTerm}) (source target : theory.Term) :
    (coarsen theory).Step source target ↔ Relation.TransGen theory.Step source target :=
  Iff.rfl

private theorem multiStep_of_transGen (theory : GSLT.{uTerm}) {source middle : theory.Term}
    (path : Relation.TransGen theory.rewrites source middle) :
    ∀ target, theory.MultiStep middle target → theory.MultiStep source target := by
  induction path with
  | single step => exact fun target rest => .step step rest
  | tail _ step ih => exact fun target rest => ih target (.step step rest)

private theorem multiStep_of_coarse (theory : GSLT.{uTerm}) :
    {source target : theory.Term} → (coarsen theory).MultiStep source target →
      theory.MultiStep source target
  | _, _, .refl term => GSLT.MultiStep.refl (S := theory) term
  | _, _, .step path rest => multiStep_of_transGen theory path _ (multiStep_of_coarse theory rest)

private theorem coarse_of_multiStep (theory : GSLT.{uTerm}) :
    {source target : theory.Term} → theory.MultiStep source target →
      (coarsen theory).MultiStep source target
  | _, _, .refl term => GSLT.MultiStep.refl (S := coarsen theory) term
  | _, _, .step step rest =>
      GSLT.MultiStep.step (S := coarsen theory) (Relation.TransGen.single step)
        (coarse_of_multiStep theory rest)

/-- Coarsening keeps reachability. -/
theorem coarsen_multiStep_iff (theory : GSLT.{uTerm}) (source target : theory.Term) :
    (coarsen theory).MultiStep source target ↔ theory.MultiStep source target :=
  ⟨multiStep_of_coarse theory, coarse_of_multiStep theory⟩

/-- A native predicate defined by reaching a goal is the same before and after
coarsening. -/
theorem coarsen_reaches_eq (theory : GSLT.{uTerm}) (goal : theory.Term → Prop) :
    (fun term : theory.Term => ∃ target, (coarsen theory).MultiStep term target ∧ goal target) =
      fun term => ∃ target, theory.MultiStep term target ∧ goal target := by
  funext term
  apply propext
  constructor
  · rintro ⟨target, reaches, reached⟩
    exact ⟨target, (coarsen_multiStep_iff theory term target).mp reaches, reached⟩
  · rintro ⟨target, reaches, reached⟩
    exact ⟨target, (coarsen_multiStep_iff theory term target).mpr reaches, reached⟩

/-- The one-step diamond of the coarsening is the transitive diamond underneath. -/
theorem coarsen_diamond_iff (theory : GSLT.{uTerm}) (predicate : theory.Term → Prop)
    (source : theory.Term) :
    gsltDiamond (coarsen theory) predicate source ↔
      ∃ target, Relation.TransGen theory.Step source target ∧ predicate target :=
  gsltDiamond_spec (coarsen theory) predicate source

/-- The one-step box of the coarsening ranges over every nonempty path underneath. -/
theorem coarsen_box_iff (theory : GSLT.{uTerm}) (predicate : theory.Term → Prop)
    (target : theory.Term) :
    gsltBox (coarsen theory) predicate target ↔
      ∀ source, Relation.TransGen theory.Step source target → predicate source :=
  gsltBox_spec (coarsen theory) predicate target

/-- Reaching in exactly `n` steps. -/
inductive StepsIn (theory : GSLT.{uTerm}) : ℕ → theory.Term → theory.Term → Prop where
  | zero (term : theory.Term) : StepsIn theory 0 term term
  | succ {n : ℕ} {source middle target : theory.Term} :
      theory.Step source middle → StepsIn theory n middle target →
        StepsIn theory (n + 1) source target

theorem StepsIn.append {theory : GSLT.{uTerm}} {m n : ℕ} {source middle target : theory.Term}
    (first : StepsIn theory m source middle) (second : StepsIn theory n middle target) :
    StepsIn theory (m + n) source target := by
  induction first with
  | zero => simpa using second
  | succ step _ ih =>
      have joined := StepsIn.succ step (ih second)
      rwa [Nat.add_right_comm] at joined

theorem StepsIn.single {theory : GSLT.{uTerm}} {source target : theory.Term}
    (step : theory.Step source target) : StepsIn theory 1 source target :=
  .succ step (.zero target)

/-- A nonempty path is a positive number of steps. -/
theorem transGen_iff_stepsIn (theory : GSLT.{uTerm}) (source target : theory.Term) :
    Relation.TransGen theory.Step source target ↔ ∃ n, 0 < n ∧ StepsIn theory n source target := by
  constructor
  · intro path
    induction path with
    | single step => exact ⟨1, Nat.one_pos, .single step⟩
    | tail _ step ih =>
        obtain ⟨n, positive, steps⟩ := ih
        exact ⟨n + 1, Nat.succ_pos n, steps.append (.single step)⟩
  · rintro ⟨n, positive, steps⟩
    induction steps with
    | zero => exact absurd positive (Nat.lt_irrefl 0)
    | @succ m _ _ _ step rest ih =>
        cases m with
        | zero =>
            cases rest
            exact .single step
        | succ m => exact .head step (ih (Nat.succ_pos m))

/-- Each coarse step stands for at least one step underneath: `k` coarse steps cost at
least `k` steps of the finer system. -/
theorem coarse_stepsIn_load (theory : GSLT.{uTerm}) :
    {k : ℕ} → {source target : theory.Term} → StepsIn (coarsen theory) k source target →
      ∃ n, k ≤ n ∧ StepsIn theory n source target
  | _, _, _, .zero term => ⟨0, le_rfl, StepsIn.zero (theory := theory) term⟩
  | _, _, _, .succ step rest => by
      obtain ⟨n, atLeast, fine⟩ := coarse_stepsIn_load theory rest
      obtain ⟨m, positive, first⟩ := (transGen_iff_stepsIn theory _ _).mp step
      exact ⟨m + n, by omega, first.append fine⟩

/-- Any nonempty path underneath is one coarse step. -/
theorem coarse_step_of_stepsIn (theory : GSLT.{uTerm}) {n : ℕ} {source target : theory.Term}
    (steps : StepsIn theory n source target) (positive : 0 < n) :
    (coarsen theory).Step source target :=
  (transGen_iff_stepsIn theory source target).mpr ⟨n, positive, steps⟩

end Coarsening

/-! ## Controls -/

namespace Controls

/-- Judgments are numbers. The axioms are the multiples of ten, and a conversion adds
one. Explicit evidence for an axiom is its quotient by ten; for a conversion, the
difference. -/
def theory : Theory ℕ where
  axioms judgment := judgment % 10 = 0
  conversion source target := target = source + 1

def axiomExplicit : TimedChecker ℕ ℕ where
  check judgment quotient := decide (judgment = 10 * quotient)
  claimSize := Nat.size
  certificateSize := Nat.size
  time judgment quotient := judgment.size + quotient.size + 1

def conversionExplicit : TimedChecker (ConversionClaim ℕ) ℕ :=
  VerificationTiers.Controls.conversionChecker

theorem axiomExplicit_sound : axiomExplicit.Sound theory.axioms := by
  intro judgment quotient accepted
  simp only [axiomExplicit, decide_eq_true_eq] at accepted
  simp only [theory]
  omega

theorem conversionExplicit_sound :
    conversionExplicit.Sound (fun claim => theory.conversion claim.source claim.target) := by
  intro claim difference accepted
  simp only [conversionExplicit, VerificationTiers.Controls.conversionChecker,
    decide_eq_true_eq] at accepted
  simp only [theory]
  omega

/-- The producer of axiom evidence: divide by ten. -/
def axiomProducer : TimedProducer axiomExplicit theory.axioms where
  produce judgment := some (judgment / 10)
  complete judgment isAxiom := ⟨judgment / 10, rfl, by
    simp only [axiomExplicit, decide_eq_true_eq]
    simp only [theory] at isAxiom
    omega⟩
  produceTime judgment := judgment.size
  writes judgment quotient produced := by
    simp only [Option.some.injEq] at produced
    subst produced
    exact Nat.size_le_size (Nat.div_le_self judgment 10)

/-- The producer of conversion evidence: the difference one. -/
def conversionProducer :
    TimedProducer conversionExplicit (fun claim => theory.conversion claim.source claim.target) where
  produce _ := some 1
  complete claim converts := ⟨1, rfl, by
    simp only [theory] at converts
    simp [conversionExplicit, VerificationTiers.Controls.conversionChecker, converts]⟩
  produceTime _ := 1
  writes _ difference produced := by
    simp only [Option.some.injEq] at produced
    subst produced
    simp [conversionExplicit, VerificationTiers.Controls.conversionChecker]

def axiomDecided : TimedChecker ℕ Unit :=
  decisionTimed (decisionKernelOfProducer axiomExplicit_sound axiomProducer.toCompleteProducer)
    Nat.size axiomProducer.decisionTime

def conversionDecided : TimedChecker (ConversionClaim ℕ) Unit :=
  decisionTimed
    (decisionKernelOfProducer conversionExplicit_sound conversionProducer.toCompleteProducer)
    (fun claim => claim.source.size + claim.target.size) conversionProducer.decisionTime

/-- Full evidence for both kinds of step. -/
def bottom : Tier ℕ ℕ ℕ := ⟨axiomExplicit, conversionExplicit⟩

/-- Axioms with evidence, conversions recomputed. -/
def middle : Tier ℕ ℕ Unit := ⟨axiomExplicit, conversionDecided⟩

/-- Both kinds recomputed: the articles are skeletons. -/
def top : Tier ℕ Unit Unit := ⟨axiomDecided, conversionDecided⟩

def middleAboveBottom : Above middle bottom where
  axiomElaboration := Elaboration.identity _
  conversionElaboration := producerElaboration conversionExplicit_sound conversionProducer

def topAboveMiddle : Above top middle where
  axiomElaboration := producerElaboration axiomExplicit_sound axiomProducer
  conversionElaboration := Elaboration.identity _

def topAboveBottom : Above top bottom := topAboveMiddle.trans middleAboveBottom

theorem bottom_locallySound : bottom.LocallySound theory :=
  ⟨axiomExplicit_sound, conversionExplicit_sound⟩

/-- The top tier is sound because the bottom is, through the elaborations. -/
theorem top_locallySound : top.LocallySound theory := topAboveBottom.sound bottom_locallySound

/-- The skeleton for `12`: the axiom `10`, then two conversions. -/
def twelveSkeleton : ExplicitCertificate ℕ Unit Unit := .convert 11 (.convert 10 (.base ()) ()) ()

/-- Its elaboration at the bottom: the quotient and both differences written in. -/
def twelveArticle : ExplicitCertificate ℕ ℕ ℕ := .convert 11 (.convert 10 (.base 1) 1) 1

example : (top.checker Nat.size).check 12 twelveSkeleton = true := by
  simp [Tier.checker, explicitTimed, explicitChecker, checkExplicit, top, axiomDecided,
    conversionDecided, decisionTimed, DecisionKernel.toChecker, decisionKernelOfProducer,
    checkProduced, axiomProducer, conversionProducer, axiomExplicit, conversionExplicit,
    VerificationTiers.Controls.conversionChecker, twelveSkeleton]

example : (topAboveBottom.elaboration Nat.size).elaborate 12 twelveSkeleton = some twelveArticle :=
  rfl

example : (bottom.checker Nat.size).check 12 twelveArticle = true := by
  simp [Tier.checker, explicitTimed, explicitChecker, checkExplicit, bottom, axiomExplicit,
    conversionExplicit, VerificationTiers.Controls.conversionChecker, twelveArticle]

/-- The same skeleton does not prove `13`, at the top or after elaboration. -/
example : (top.checker Nat.size).check 13 twelveSkeleton = false := by
  simp [Tier.checker, explicitTimed, explicitChecker, checkExplicit, top, axiomDecided,
    conversionDecided, decisionTimed, DecisionKernel.toChecker, decisionKernelOfProducer,
    checkProduced, axiomProducer, conversionProducer, axiomExplicit, conversionExplicit,
    VerificationTiers.Controls.conversionChecker, twelveSkeleton]

example : (bottom.checker Nat.size).check 13 twelveArticle = false := by
  simp [Tier.checker, explicitTimed, explicitChecker, checkExplicit, bottom, axiomExplicit,
    conversionExplicit, VerificationTiers.Controls.conversionChecker, twelveArticle]

/-- Moving down costs exactly the evidence written in: the article is the skeleton plus
the bits of the quotient and the two differences. -/
example : (bottom.checker Nat.size).certificateSize twelveArticle =
    skeletonSize Nat.size twelveSkeleton.erase +
      evidenceSize Nat.size Nat.size twelveArticle :=
  liftArticle_size Nat.size Nat.size Nat.size
    (show liftArticle (topAboveBottom.axiomElaboration.elaborate)
      (topAboveBottom.conversionElaboration.elaborate) 12 twelveSkeleton = some twelveArticle from rfl)

/-- A trusted axiom checker that accepts everything. -/
def axiomTrustedWrong : TimedChecker ℕ Unit where
  check _ _ := true
  claimSize := Nat.size
  certificateSize _ := 0
  time _ _ := 0

def trustedWrong : Tier ℕ Unit Unit := ⟨axiomTrustedWrong, conversionDecided⟩

/-- It is unsound, so it lies above no sound tier. -/
theorem trustedWrong_not_above : ¬ Nonempty (Above trustedWrong bottom) := by
  refine not_above_of_unsound (theory := theory) ?_ bottom_locallySound
  rintro ⟨axiomSound, _⟩
  have three := axiomSound 3 () rfl
  simp [theory] at three

/-- A correct axiom kernel charged no time, as native code would be. -/
def axiomTrustedFast : TimedChecker ℕ Unit where
  check judgment _ := decide (judgment % 10 = 0)
  claimSize := Nat.size
  certificateSize _ := 0
  time _ _ := 0

/-- It elaborates into the explicit axiom checker, but no elaboration of it writes
within its time: the evidence for `1000` has seven bits. -/
theorem axiomTrustedFast_not_traceBounded
    (elaboration : Elaboration axiomTrustedFast.toChecker axiomExplicit.toChecker) :
    ¬ elaboration.TraceBounded (computing := axiomTrustedFast)
      (explicit := axiomExplicit.toSizedChecker) := by
  refine not_traceBounded_of_fast elaboration (claim := 1000) (certificate := ()) (by decide) ?_
  intro quotient accepted
  change decide (1000 = 10 * quotient) = true at accepted
  have quotientEq : quotient = 100 := by
    simp only [decide_eq_true_eq] at accepted
    omega
  subst quotientEq
  change 0 < Nat.size 100
  decide

/-- A counting system: each step adds one. -/
abbrev counting : GSLT.{0} where
  Term := ℕ
  equations := ⟨Eq, eq_equivalence⟩
  rewrites source target := target = source + 1
  rewrites_resp_left := by
    rintro t t' u rfl step
    exact ⟨u, step, rfl⟩
  rewrites_resp_right := by
    rintro t u u' step rfl
    exact step

theorem counting_stepsIn : ∀ n : ℕ, StepsIn counting n (0 : ℕ) n
  | 0 => StepsIn.zero (theory := counting) (0 : ℕ)
  | n + 1 => (counting_stepsIn n).append (.single (show n + 1 = n + 1 from rfl))

/-- Counting steps add their number. -/
theorem counting_steps_add :
    {m : ℕ} → {source target : counting.Term} → StepsIn counting m source target →
      @Eq ℕ target (source + m)
  | _, _, _, .zero _ => rfl
  | _, source, target, @StepsIn.succ _ n _ middle _ step rest => by
      have first : @Eq ℕ middle (source + 1) := step
      have later : @Eq ℕ target (middle + n) := counting_steps_add rest
      show @Eq ℕ target (source + (n + 1))
      omega

/-- Five counting steps are one coarse step. -/
example : (coarsen counting).Step (0 : ℕ) (5 : ℕ) :=
  coarse_step_of_stepsIn counting (counting_stepsIn 5) (by decide)

/-- A coarse step is never empty. -/
example : ¬ (coarsen counting).Step (3 : ℕ) (3 : ℕ) := by
  intro path
  obtain ⟨n, positive, steps⟩ := (transGen_iff_stepsIn counting 3 3).mp path
  have := counting_steps_add steps
  omega

end Controls

end Mettapedia.GSLT.LanguageDef.TierLattice
