import Mettapedia.GSLT.LanguageDef.TierLattice
import Mettapedia.GSLT.LanguageDef.BootstrapCell.ReplayCorrect
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralConversionPaths
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.UniverseProfiles
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TwoSortConservativity
import Mettapedia.TypeTheory.NbE.EnvironmentMachine

/-!
# Verified Rungs and Observer-Indexed Fibered Bubble Carve-Outs

`TierLattice.Above` orders verification tiers by per-run certificate elaboration:
an upper tier lies above a lower tier when every upper certificate can be elaborated
per run into a lower explicit certificate (`Above.elaboration`), and `Above.Writes`
charges the upper checker at least the size of the elaborated certificate.

Beside `TierLattice.Above`, this module introduces:

1. **The Verified-Rung Relation (`VerifiedRung`)**:
   A lower tier (or host proof tier) holds a once-and-for-all soundness proof for
   the upper tier's conversion `DecisionKernel` (`ConversionEvidence = Unit`).
   Because the conversion procedure is proved correct by construction rather than
   trusted as an external oracle or elaborated per run:
   - it needs **no per-run conversion certificates** (`certificateSize () = 0`,
     `evidenceSize = 0` on conversions);
   - it transfers `Tier.LocallySound` and `Checker.Sound (Derivable theory)` to the
     upper tier without constructing an `Elaboration` into explicit conversion trees;
   - it qualifies directly at the NIK Stage A boundary (`ReplaySignature`,
     `ReplayCorrect`, `SemanticQualification`, `DecisionKernel.authority`).

2. **Observer-Indexed Fibered Bubble Carve-Outs (`FiberedBubble`)**:
   A weaker layer ("bubble") is carved out of a stronger top theory by an embedding
   and syntactic retraction that preserve three things simultaneously:
   - **the judgment** (`judgment_iff`): derivability in the bubble coincides with
     derivability of the embedded claim in the carved-out top subjudgment;
   - **the computation** (`step_iff`, `reduces_iff`, `conv_iff`): operational steps,
     multi-step reductions, and symmetric conversions are preserved and reflected
     so computation preservation is never silently lost;
   - **the observer's observations** (`observe_commutes`, `observe_step_invariant`):
     what the observer observes commutes with the carve-out and is respected by the
     operational semantics.
   We instantiate `FiberedBubble` with the embedding of the one-universe `Legacy`
   profile into the cumulative `Tower` profile of `ParameterizedPiSigmaId`, and
   contrast it with the negative control where unrestricted `Tower.HasType` fails
   judgment reflection (`Legacy.unrestricted_raw_reflection_is_false`).

3. **Concrete Separation Instantiating `TierLattice.not_traceBounded_of_fast`**:
   For the family of $N$-step $\beta$-chains `idBetaChain steps base ≡ base` in
   `ParameterizedPiSigmaId`:
   - Every accepted explicit conversion certificate `code : StructuralConversionCode.Code`
     in the format must have `1 ≤ code.stepCount` (when `steps ≥ 1`) and syntactic
     certificate size `3 * steps + tmNodeCount base ≤ code.certSize`
     (`explicitConversion_certSize_lower_bound`).
   - The canonical step-by-step explicit trace `idBetaChainCode steps base` has
     exact quadratic syntactic size
     `2 * codeCertSize _ (idBetaChainCode steps base) = 6 * steps * (steps - 1) + 2 * steps * (2 * tmNodeCount base + 3) + 2 * tmNodeCount base`
     (`codeCertSize_idBetaChainCode_quadratic`).
   - Meanwhile, our instrumented closure-based weak-head machine `nbeWhnfSteps`
     evaluates `idBetaChain steps (.pi A B)` in **exactly `3 * steps + 1` recursive
     calls** (`nbeWhnfSteps_idBetaChain_pi`), independent of `tmNodeCount A` and
     `tmNodeCount B`, because closures bind arguments in $O(1)$ without substituting
     or copying `.pi A B`.
   - Instantiating `TierLattice.not_traceBounded_of_fast` with `decideTime` set to
     the **actual instrumented closure-machine step count** `nbeWhnfSteps`
     (`verifiedRung_not_traceBounded_of_nbeWhnfSteps`), no elaboration from the
     verified conversion rung to explicit `StructuralConversionCode` certificates
     is trace-bounded.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.NbE

open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.KernelAuthority.Checker
open Mettapedia.GSLT.LanguageDef.ProofSystems
open Mettapedia.GSLT.LanguageDef.VerificationTiers
open Mettapedia.GSLT.LanguageDef.TierLattice
open Mettapedia.GSLT.LanguageDef.BootstrapCell
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation

universe uJudgment uAxiom uConversion uBubble uTop uBubbleJudg uTopJudg uObs

/-! ## 1. The Verified-Rung Relation -/

section VerifiedRung

variable {Judgment : Type uJudgment}
  {UpperAxiom : Type uAxiom}
  {LowerAxiom : Type uAxiom}
  {LowerConversion : Type uConversion}

/-- A verified conversion rung between an upper tier whose conversion slot is a
verified `DecisionKernel` (`Unit` conversion evidence, zero per-run conversion
certificate) and a lower explicit tier for the same `theory : Theory Judgment`.

Unlike `TierLattice.Above`, which requires a per-run `Elaboration` from upper
conversion certificates to lower conversion certificates, a `VerifiedRung` carries
the lower tier's once-and-for-all proof that the upper conversion decision kernel is
correct for `theory.conversion`. -/
structure VerifiedRung (theory : Theory Judgment)
    (upper : Tier Judgment UpperAxiom Unit)
    (lower : Tier Judgment LowerAxiom LowerConversion) where
  /-- Axiom evidence elaborates into the lower tier's axiom checker. -/
  axiomElaboration : Elaboration upper.axiomChecker.toChecker lower.axiomChecker.toChecker
  /-- The upper tier's conversion slot is backed by a verified decision kernel. -/
  conversionKernel :
    DecisionKernel (ConversionClaim Judgment)
      (fun claim => theory.conversion claim.source claim.target)
  /-- The upper tier's conversion checker agrees with the verified decision kernel. -/
  conversionCheck_eq :
    ∀ (claim : ConversionClaim Judgment) (u : Unit),
      upper.conversionChecker.check claim u = conversionKernel.decide claim
  /-- Per-run conversion certificates carry zero size. -/
  conversionCertSize_zero :
    ∀ (u : Unit), upper.conversionChecker.certificateSize u = 0

namespace VerifiedRung

variable {theory : Theory Judgment}
  {upper : Tier Judgment UpperAxiom Unit}
  {lower : Tier Judgment LowerAxiom LowerConversion}

/-- Build an upper `Tier` directly from an axiom checker, a verified conversion
`DecisionKernel`, and a local time function for conversion decisions. -/
def tierOfDecisionKernel
    (axiomChecker : TimedChecker Judgment UpperAxiom)
    (conversionKernel :
      DecisionKernel (ConversionClaim Judgment)
        (fun claim => theory.conversion claim.source claim.target))
    (claimSize : ConversionClaim Judgment → Nat)
    (decideTime : ConversionClaim Judgment → Nat) :
    Tier Judgment UpperAxiom Unit where
  axiomChecker := axiomChecker
  conversionChecker := decisionTimed conversionKernel claimSize decideTime

/-- Canonical `VerifiedRung` when the upper tier is built via `tierOfDecisionKernel`. -/
def ofDecisionKernel
    {axiomChecker : TimedChecker Judgment UpperAxiom}
    (lower : Tier Judgment LowerAxiom LowerConversion)
    (axiomElaboration : Elaboration axiomChecker.toChecker lower.axiomChecker.toChecker)
    (conversionKernel :
      DecisionKernel (ConversionClaim Judgment)
        (fun claim => theory.conversion claim.source claim.target))
    (claimSize : ConversionClaim Judgment → Nat)
    (decideTime : ConversionClaim Judgment → Nat) :
    VerifiedRung theory
      (tierOfDecisionKernel axiomChecker conversionKernel claimSize decideTime)
      lower where
  axiomElaboration := axiomElaboration
  conversionKernel := conversionKernel
  conversionCheck_eq _ _ := rfl
  conversionCertSize_zero _ := rfl

/-- The upper conversion checker has full `Authority` (both soundness and
completeness with respect to `Unit` certificates) over `theory.conversion`. -/
theorem conversion_authority (rung : VerifiedRung theory upper lower) :
    upper.conversionChecker.Authority
      (fun claim => theory.conversion claim.source claim.target) where
  sound claim u accepted := by
    rw [rung.conversionCheck_eq claim u] at accepted
    exact (rung.conversionKernel.correct claim).mp accepted
  complete claim holds := by
    refine ⟨(), ?_⟩
    rw [rung.conversionCheck_eq claim ()]
    exact (rung.conversionKernel.correct claim).mpr holds

/-- A verified rung transfers `LocallySound` to the upper tier assuming only that the
lower tier's axiom checker is sound, with **no** lower conversion certificate or
conversion elaborator required. -/
theorem locallySound_of_lowerAxiomSound (rung : VerifiedRung theory upper lower)
    (lowerAxiomSound : lower.axiomChecker.Sound theory.axioms) :
    upper.LocallySound theory :=
  ⟨rung.axiomElaboration.sound lowerAxiomSound, rung.conversion_authority.sound⟩

/-- In particular, if the lower tier is `LocallySound`, then the upper tier is
`LocallySound` via the verified rung. -/
theorem sound (rung : VerifiedRung theory upper lower)
    (lowerSound : lower.LocallySound theory) :
    upper.LocallySound theory :=
  rung.locallySound_of_lowerAxiomSound lowerSound.1

/-- Consequently, the full upper-tier article checker is sound for `Derivable theory`
without per-run conversion certificates. -/
theorem checker_sound (rung : VerifiedRung theory upper lower)
    (lowerSound : lower.LocallySound theory) (judgmentSize : Judgment → Nat) :
    (upper.checker judgmentSize).Sound (Derivable theory) :=
  Tier.checker_sound judgmentSize (rung.sound lowerSound)

/-- A verified rung needs **zero** per-run conversion certificate space:
for any upper-tier article, its `evidenceSize` equals the `evidenceSize` computed
with zero conversion certificate size (`fun _ => 0`), i.e., solely its base axiom
evidence size. -/
theorem no_per_run_conversion_certificates (rung : VerifiedRung theory upper lower)
    (article : ExplicitCertificate Judgment UpperAxiom Unit) :
    evidenceSize upper.axiomChecker.certificateSize
      upper.conversionChecker.certificateSize article =
    evidenceSize upper.axiomChecker.certificateSize (fun _ => 0) article := by
  induction article with
  | base ev => rfl
  | convert source prior u ih =>
      simp [evidenceSize, rung.conversionCertSize_zero u, ih]

/-- Adding any number of `.convert` steps on a `VerifiedRung` adds zero to `evidenceSize`. -/
@[simp] theorem evidenceSize_convert (rung : VerifiedRung theory upper lower)
    (source : Judgment) (prior : ExplicitCertificate Judgment UpperAxiom Unit) :
    evidenceSize upper.axiomChecker.certificateSize
      upper.conversionChecker.certificateSize (.convert source prior ()) =
    evidenceSize upper.axiomChecker.certificateSize
      upper.conversionChecker.certificateSize prior := by
  simp [evidenceSize, rung.conversionCertSize_zero ()]

/-- The total article size on a `VerifiedRung` equals its erased skeleton size plus
only the base axiom evidence size (zero per-run conversion certificate overhead). -/
theorem explicitSize_eq_skeleton_plus_base (rung : VerifiedRung theory upper lower)
    (judgmentSize : Judgment → Nat)
    (article : ExplicitCertificate Judgment UpperAxiom Unit) :
    explicitSize judgmentSize upper.axiomChecker.certificateSize
      upper.conversionChecker.certificateSize article =
    skeletonSize judgmentSize article.erase +
      evidenceSize upper.axiomChecker.certificateSize (fun _ => 0) article := by
  rw [explicitSize_eq, rung.no_per_run_conversion_certificates]

/-- Stage A `ReplaySignature` for a verified conversion rung's decision kernel
(when conversion claims have decidable equality): a zero-premise rule step is
admitted for `claim` iff `conversionKernel.decide claim = true`. -/
def conversionReplaySignature [DecidableEq (ConversionClaim Judgment)]
    (rung : VerifiedRung theory upper lower)
    (decodeClaim :
      Mettapedia.GSLT.LanguageDef.InferenceChecker.RuleInstance →
        Option (ConversionClaim Judgment)) :
    ReplaySignature where
  Goal := ConversionClaim Judgment
  decEq := inferInstance
  step label :=
    match decodeClaim label with
    | some claim =>
        if rung.conversionKernel.decide claim then some ([], claim) else none
    | none => none

/-- Stage A `ReplayCorrect` witness for the verified conversion rung's replay signature. -/
theorem conversionReplaySignature_correct [DecidableEq (ConversionClaim Judgment)]
    (rung : VerifiedRung theory upper lower)
    (decodeClaim :
      Mettapedia.GSLT.LanguageDef.InferenceChecker.RuleInstance →
        Option (ConversionClaim Judgment)) :
    ReplayCorrect
      (rung.conversionReplaySignature decodeClaim)
      (rung.conversionReplaySignature decodeClaim).replay :=
  replay_correct (rung.conversionReplaySignature decodeClaim)

/-- Stage A `SemanticQualification` for the verified conversion rung's replay signature:
every accepted goal satisfies `theory.conversion claim.source claim.target`. -/
def conversionSemanticQualification [DecidableEq (ConversionClaim Judgment)]
    (rung : VerifiedRung theory upper lower)
    (decodeClaim :
      Mettapedia.GSLT.LanguageDef.InferenceChecker.RuleInstance →
        Option (ConversionClaim Judgment)) :
    SemanticQualification (rung.conversionReplaySignature decodeClaim) where
  Meaning claim := theory.conversion claim.source claim.target
  closed label premises conclusion hStep _ := by
    simp only [conversionReplaySignature] at hStep
    cases hDec : decodeClaim label with
    | none => simp [hDec] at hStep
    | some claim =>
        simp only [hDec] at hStep
        split at hStep
        · rename_i hAccept
          rcases Prod.mk.inj (Option.some.inj hStep) with ⟨_, rfl⟩
          exact (rung.conversionKernel.correct claim).mp hAccept
        · cases hStep

end VerifiedRung
end VerifiedRung

/-! ## 2. Observer-Indexed Fibered Bubble Carve-Outs -/

/-- An **observer-indexed fibered bubble carve-out** from a top theory (`TopTerm`,
`TopJudgment`) into a weaker specialized layer (`BubbleTerm`, `BubbleJudgment`)
under an observation interface `Obs`.

A valid bubble carve-out preserves three things simultaneously:
1. **The judgment** (`judgment_iff`): a bubble judgment holds iff its image in the
   carved-out top judgment holds;
2. **The computation** (`step_to_top`, `step_of_top`, and derived `step_iff`,
   `reduces_iff`, `conv_iff`): operational computation is both preserved along
   `embedTerm` and reflected along the syntactic retraction `forgetTerm`;
3. **The observer's observations** (`observe_commutes` and `observe_step_invariant`):
   the observer's view of bubble terms agrees with its view in the top theory and
   is preserved along computation. -/
structure FiberedBubble
    (BubbleTerm : Type uBubble) (TopTerm : Type uTop)
    (BubbleJudgment : Type uBubbleJudg) (TopJudgment : Type uTopJudg)
    (Obs : Type uObs) where
  embedTerm : BubbleTerm → TopTerm
  forgetTerm : TopTerm → BubbleTerm
  forget_embed : ∀ b : BubbleTerm, forgetTerm (embedTerm b) = b
  embedJudgment : BubbleJudgment → TopJudgment
  bubbleDerivable : BubbleJudgment → Prop
  topDerivable : TopJudgment → Prop
  bubbleStep : BubbleTerm → BubbleTerm → Prop
  topStep : TopTerm → TopTerm → Prop
  /-- (1) Judgment preservation and reflection (conservativity on the carved-out fiber). -/
  judgment_iff : ∀ j : BubbleJudgment, bubbleDerivable j ↔ topDerivable (embedJudgment j)
  /-- (2a) One-step computation preservation into the top theory. -/
  step_to_top : ∀ {x y : BubbleTerm}, bubbleStep x y → topStep (embedTerm x) (embedTerm y)
  /-- (2b) One-step computation projection from the top theory via `forgetTerm`. -/
  step_of_top : ∀ {x y : TopTerm}, topStep x y → bubbleStep (forgetTerm x) (forgetTerm y)
  /-- (3) Observer projection on the bubble and on the top theory. -/
  bubbleObserve : BubbleTerm → Obs
  topObserve : TopTerm → Obs
  observe_commutes : ∀ x : BubbleTerm, topObserve (embedTerm x) = bubbleObserve x
  observe_step_invariant : ∀ {x y : BubbleTerm}, bubbleStep x y → bubbleObserve x = bubbleObserve y

namespace FiberedBubble

variable {BTerm : Type uBubble} {TTerm : Type uTop}
  {BJudg : Type uBubbleJudg} {TJudg : Type uTopJudg} {Obs : Type uObs}

/-- `embedTerm` is automatically injective because `forgetTerm` is a left inverse. -/
theorem embedTerm_injective (B : FiberedBubble BTerm TTerm BJudg TJudg Obs) :
    Function.Injective B.embedTerm := by
  intro x y h
  have := congrArg B.forgetTerm h
  simpa [B.forget_embed] using this

/-- One-step computation is both preserved and reflected on the bubble. -/
theorem step_iff (B : FiberedBubble BTerm TTerm BJudg TJudg Obs) (x y : BTerm) :
    B.bubbleStep x y ↔ B.topStep (B.embedTerm x) (B.embedTerm y) := by
  constructor
  · exact B.step_to_top
  · intro hTop
    have := B.step_of_top hTop
    simpa [B.forget_embed] using this

/-- Multi-step reduction in the top theory projects to multi-step reduction in the bubble. -/
theorem reduces_of_top (B : FiberedBubble BTerm TTerm BJudg TJudg Obs) {x y : TTerm}
    (red : Relation.ReflTransGen B.topStep x y) :
    Relation.ReflTransGen B.bubbleStep (B.forgetTerm x) (B.forgetTerm y) := by
  induction red with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (B.step_of_top step)

/-- Reflexive-transitive computation in the bubble is preserved and reflected in the
top theory. -/
theorem reduces_iff (B : FiberedBubble BTerm TTerm BJudg TJudg Obs) (x y : BTerm) :
    Relation.ReflTransGen B.bubbleStep x y ↔
      Relation.ReflTransGen B.topStep (B.embedTerm x) (B.embedTerm y) := by
  constructor
  · intro red
    induction red with
    | refl => exact .refl
    | tail _ step ih => exact ih.tail (B.step_to_top step)
  · intro topRed
    have hProj := B.reduces_of_top topRed
    simpa [B.forget_embed] using hProj

/-- Conversion in the top theory projects to conversion in the bubble. -/
theorem conv_of_top (B : FiberedBubble BTerm TTerm BJudg TJudg Obs) {x y : TTerm}
    (conv : Relation.EqvGen B.topStep x y) :
    Relation.EqvGen B.bubbleStep (B.forgetTerm x) (B.forgetTerm y) := by
  induction conv with
  | rel _ _ step => exact .rel _ _ (B.step_of_top step)
  | refl _ => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ih1 ih2 => exact .trans _ _ _ ih1 ih2

/-- Symmetric-reflexive-transitive conversion in the bubble is preserved and reflected
in the top theory. -/
theorem conv_iff (B : FiberedBubble BTerm TTerm BJudg TJudg Obs) (x y : BTerm) :
    Relation.EqvGen B.bubbleStep x y ↔
      Relation.EqvGen B.topStep (B.embedTerm x) (B.embedTerm y) := by
  constructor
  · intro conv
    induction conv with
    | rel _ _ step => exact .rel _ _ (B.step_to_top step)
    | refl _ => exact .refl _
    | symm _ _ _ ih => exact .symm _ _ ih
    | trans _ _ _ _ _ ih1 ih2 => exact .trans _ _ _ ih1 ih2
  · intro topConv
    have hProj := B.conv_of_top topConv
    simpa [B.forget_embed] using hProj

/-- Observer observations are invariant across arbitrary multi-step computations
in the bubble, and match the top theory's observations at both endpoints. -/
theorem observe_reduces_invariant (B : FiberedBubble BTerm TTerm BJudg TJudg Obs)
    {x y : BTerm} (red : Relation.ReflTransGen B.bubbleStep x y) :
    B.bubbleObserve x = B.bubbleObserve y ∧
      B.topObserve (B.embedTerm x) = B.topObserve (B.embedTerm y) := by
  have hBubble : B.bubbleObserve x = B.bubbleObserve y := by
    induction red with
    | refl => rfl
    | tail _ step ih => exact ih.trans (B.observe_step_invariant step)
  refine ⟨hBubble, ?_⟩
  rw [B.observe_commutes x, B.observe_commutes y, hBubble]

/-- Observer observations are invariant across arbitrary conversions in the bubble,
and match the top theory's observations at both endpoints. -/
theorem observe_conv_invariant (B : FiberedBubble BTerm TTerm BJudg TJudg Obs)
    {x y : BTerm} (conv : Relation.EqvGen B.bubbleStep x y) :
    B.bubbleObserve x = B.bubbleObserve y ∧
      B.topObserve (B.embedTerm x) = B.topObserve (B.embedTerm y) := by
  have hBubble : B.bubbleObserve x = B.bubbleObserve y := by
    induction conv with
    | rel _ _ step => exact B.observe_step_invariant step
    | refl _ => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
  refine ⟨hBubble, ?_⟩
  rw [B.observe_commutes x, B.observe_commutes y, hBubble]

/-- A verified `DecisionKernel` for the top theory's judgment pulls back along a
`FiberedBubble` to a verified `DecisionKernel` for the bubble's judgment with zero
per-run certificate overhead. -/
def pullBackDecisionKernel (B : FiberedBubble BTerm TTerm BJudg TJudg Obs)
    (topKernel : DecisionKernel TJudg B.topDerivable) :
    DecisionKernel BJudg B.bubbleDerivable where
  decide j := topKernel.decide (B.embedJudgment j)
  correct j := (topKernel.correct (B.embedJudgment j)).trans (B.judgment_iff j).symm

/-- Composition of nested fibered bubbles when the inner top interface matches
the outer bubble interface. -/
def comp
    {B₁Term B₂Term B₃Term : Type uBubble}
    {B₁Judg B₂Judg B₃Judg : Type uBubbleJudg}
    (inner : FiberedBubble B₁Term B₂Term B₁Judg B₂Judg Obs)
    (outer : FiberedBubble B₂Term B₃Term B₂Judg B₃Judg Obs)
    (hJudg : inner.topDerivable = outer.bubbleDerivable)
    (hStep : inner.topStep = outer.bubbleStep)
    (hObs : inner.topObserve = outer.bubbleObserve) :
    FiberedBubble B₁Term B₃Term B₁Judg B₃Judg Obs where
  embedTerm := outer.embedTerm ∘ inner.embedTerm
  forgetTerm := inner.forgetTerm ∘ outer.forgetTerm
  forget_embed b := by
    simp only [Function.comp_apply, outer.forget_embed, inner.forget_embed]
  embedJudgment := outer.embedJudgment ∘ inner.embedJudgment
  bubbleDerivable := inner.bubbleDerivable
  topDerivable := outer.topDerivable
  bubbleStep := inner.bubbleStep
  topStep := outer.topStep
  judgment_iff j := by
    have h1 := inner.judgment_iff j
    rw [hJudg] at h1
    exact h1.trans (outer.judgment_iff (inner.embedJudgment j))
  step_to_top step := by
    have h1 := inner.step_to_top step
    rw [hStep] at h1
    exact outer.step_to_top h1
  step_of_top step := by
    have h1 := outer.step_of_top step
    rw [← hStep] at h1
    exact inner.step_of_top h1
  bubbleObserve := inner.bubbleObserve
  topObserve := outer.topObserve
  observe_commutes x := by
    have h1 := outer.observe_commutes (inner.embedTerm x)
    have h2 := inner.observe_commutes x
    rw [hObs] at h2
    exact h1.trans h2
  observe_step_invariant step := inner.observe_step_invariant step

end FiberedBubble

/-! ## 3. Concrete Separation on `ParameterizedPiSigmaId` Conversion Certificates -/

namespace Separation

open StructuralConversionCode

variable {Head : Type}

/-- Syntactic node count of a scoped term `Tm Head n` (always `≥ 1`). -/
def tmNodeCount {n : Nat} : Tm Head n → Nat
  | .var _ | .const _ | .head _ => 1
  | .pi A B | .sigma A B | .app A B | .pair A B => 1 + tmNodeCount A + tmNodeCount B
  | .id A a b => 1 + tmNodeCount A + tmNodeCount a + tmNodeCount b
  | .lam body => 1 + tmNodeCount body
  | .fst p | .snd p | .refl p => 1 + tmNodeCount p

theorem tmNodeCount_pos {n : Nat} (t : Tm Head n) : 1 ≤ tmNodeCount t := by
  cases t <;> simp [tmNodeCount] <;> omega

/-- Syntactic payload size of a single structural step certificate `StepCode`. -/
def stepCertSize {RootCode : Nat → Type} (rootSize : {n : Nat} → RootCode n → Nat) :
    {n : Nat} → StepCode Head RootCode n → Nat
  | _, .betaPi body arg =>
      2 + tmNodeCount body + tmNodeCount arg + tmNodeCount (inst0 arg body)
  | _, .betaSigmaFst first second =>
      2 + tmNodeCount first + tmNodeCount second
  | _, .betaSigmaSnd first second =>
      2 + tmNodeCount first + tmNodeCount second
  | _, .head _ _ => 1
  | _, .root code => rootSize code
  | _, .congPiDom code cod => 1 + stepCertSize rootSize code + tmNodeCount cod
  | _, .congPiCod dom code => 1 + tmNodeCount dom + stepCertSize rootSize code
  | _, .congSigmaDom code cod => 1 + stepCertSize rootSize code + tmNodeCount cod
  | _, .congSigmaCod dom code => 1 + tmNodeCount dom + stepCertSize rootSize code
  | _, .congIdTy code l r =>
      1 + stepCertSize rootSize code + tmNodeCount l + tmNodeCount r
  | _, .congIdLeft ty code r =>
      1 + tmNodeCount ty + stepCertSize rootSize code + tmNodeCount r
  | _, .congIdRight ty l code =>
      1 + tmNodeCount ty + tmNodeCount l + stepCertSize rootSize code
  | _, .congLam code => 1 + stepCertSize rootSize code
  | _, .congAppFun code arg => 1 + stepCertSize rootSize code + tmNodeCount arg
  | _, .congAppArg fn code => 1 + tmNodeCount fn + stepCertSize rootSize code
  | _, .congPairFst code snd => 1 + stepCertSize rootSize code + tmNodeCount snd
  | _, .congPairSnd fst code => 1 + tmNodeCount fst + stepCertSize rootSize code
  | _, .congFst code => 1 + stepCertSize rootSize code
  | _, .congSnd code => 1 + stepCertSize rootSize code
  | _, .congRefl code => 1 + stepCertSize rootSize code

/-- Total syntactic certificate size of a `StructuralConversionCode.Code`. -/
def codeCertSize {RootCode : Nat → Type} (rootSize : {n : Nat} → RootCode n → Nat)
    {n : Nat} : Code Head RootCode n → Nat
  | .single step => stepCertSize rootSize step
  | .refl term => tmNodeCount term
  | .symm code => codeCertSize rootSize code
  | .trans first second => codeCertSize rootSize first + codeCertSize rootSize second

/-- Any decoded `StepCode` with empty root codes has certificate size at least the
syntactic node count of both its left and right endpoints. -/
theorem stepCertSize_ge_endpoints
    {headEq : Head → Head → Prop} [DecidableRel headEq]
    {n : Nat} (step : StepCode Head (fun _ => Empty) n)
    {left right : Tm Head n}
    (decoded :
      step.decode headEq (RootDecoder.ofEmpty RootComputation.empty rfl).decode =
        some (left, right)) :
    tmNodeCount left ≤ stepCertSize (fun code => nomatch code) step ∧
      tmNodeCount right ≤ stepCertSize (fun code => nomatch code) step := by
  induction step with
  | betaPi body arg =>
      simp only [StepCode.decode, Option.some.injEq, Prod.mk.injEq] at decoded
      rcases decoded with ⟨rfl, rfl⟩
      simp only [tmNodeCount, stepCertSize]
      omega
  | betaSigmaFst first second =>
      simp only [StepCode.decode, Option.some.injEq, Prod.mk.injEq] at decoded
      rcases decoded with ⟨rfl, rfl⟩
      simp only [tmNodeCount, stepCertSize]
      omega
  | betaSigmaSnd first second =>
      simp only [StepCode.decode, Option.some.injEq, Prod.mk.injEq] at decoded
      rcases decoded with ⟨rfl, rfl⟩
      simp only [tmNodeCount, stepCertSize]
      omega
  | head h₁ h₂ =>
      simp only [StepCode.decode] at decoded
      split at decoded
      · simp only [Option.some.injEq, Prod.mk.injEq] at decoded
        rcases decoded with ⟨rfl, rfl⟩
        simp [tmNodeCount, stepCertSize]
      · cases decoded
  | root empty => exact nomatch empty
  | congPiDom code cod ih =>
      simp only [StepCode.decode, mapEndpoints, Option.map_eq_some_iff] at decoded
      rcases decoded with ⟨⟨l₀, r₀⟩, hDec, hEq⟩
      rcases Prod.mk.inj hEq with ⟨rfl, rfl⟩
      have ⟨hL, hR⟩ := ih hDec
      simp only [tmNodeCount, stepCertSize]
      omega
  | congPiCod dom code ih =>
      simp only [StepCode.decode, mapEndpoints, Option.map_eq_some_iff] at decoded
      rcases decoded with ⟨⟨l₀, r₀⟩, hDec, hEq⟩
      rcases Prod.mk.inj hEq with ⟨rfl, rfl⟩
      have ⟨hL, hR⟩ := ih hDec
      simp only [tmNodeCount, stepCertSize]
      omega
  | congSigmaDom code cod ih =>
      simp only [StepCode.decode, mapEndpoints, Option.map_eq_some_iff] at decoded
      rcases decoded with ⟨⟨l₀, r₀⟩, hDec, hEq⟩
      rcases Prod.mk.inj hEq with ⟨rfl, rfl⟩
      have ⟨hL, hR⟩ := ih hDec
      simp only [tmNodeCount, stepCertSize]
      omega
  | congSigmaCod dom code ih =>
      simp only [StepCode.decode, mapEndpoints, Option.map_eq_some_iff] at decoded
      rcases decoded with ⟨⟨l₀, r₀⟩, hDec, hEq⟩
      rcases Prod.mk.inj hEq with ⟨rfl, rfl⟩
      have ⟨hL, hR⟩ := ih hDec
      simp only [tmNodeCount, stepCertSize]
      omega
  | congIdTy code l r ih =>
      simp only [StepCode.decode, mapEndpoints, Option.map_eq_some_iff] at decoded
      rcases decoded with ⟨⟨l₀, r₀⟩, hDec, hEq⟩
      rcases Prod.mk.inj hEq with ⟨rfl, rfl⟩
      have ⟨hL, hR⟩ := ih hDec
      simp only [tmNodeCount, stepCertSize]
      omega
  | congIdLeft ty code r ih =>
      simp only [StepCode.decode, mapEndpoints, Option.map_eq_some_iff] at decoded
      rcases decoded with ⟨⟨l₀, r₀⟩, hDec, hEq⟩
      rcases Prod.mk.inj hEq with ⟨rfl, rfl⟩
      have ⟨hL, hR⟩ := ih hDec
      simp only [tmNodeCount, stepCertSize]
      omega
  | congIdRight ty l code ih =>
      simp only [StepCode.decode, mapEndpoints, Option.map_eq_some_iff] at decoded
      rcases decoded with ⟨⟨l₀, r₀⟩, hDec, hEq⟩
      rcases Prod.mk.inj hEq with ⟨rfl, rfl⟩
      have ⟨hL, hR⟩ := ih hDec
      simp only [tmNodeCount, stepCertSize]
      omega
  | congLam code ih =>
      simp only [StepCode.decode, mapEndpoints, Option.map_eq_some_iff] at decoded
      rcases decoded with ⟨⟨l₀, r₀⟩, hDec, hEq⟩
      rcases Prod.mk.inj hEq with ⟨rfl, rfl⟩
      have ⟨hL, hR⟩ := ih hDec
      simp only [tmNodeCount, stepCertSize]
      omega
  | congAppFun code arg ih =>
      simp only [StepCode.decode, mapEndpoints, Option.map_eq_some_iff] at decoded
      rcases decoded with ⟨⟨l₀, r₀⟩, hDec, hEq⟩
      rcases Prod.mk.inj hEq with ⟨rfl, rfl⟩
      have ⟨hL, hR⟩ := ih hDec
      simp only [tmNodeCount, stepCertSize]
      omega
  | congAppArg fn code ih =>
      simp only [StepCode.decode, mapEndpoints, Option.map_eq_some_iff] at decoded
      rcases decoded with ⟨⟨l₀, r₀⟩, hDec, hEq⟩
      rcases Prod.mk.inj hEq with ⟨rfl, rfl⟩
      have ⟨hL, hR⟩ := ih hDec
      simp only [tmNodeCount, stepCertSize]
      omega
  | congPairFst code snd ih =>
      simp only [StepCode.decode, mapEndpoints, Option.map_eq_some_iff] at decoded
      rcases decoded with ⟨⟨l₀, r₀⟩, hDec, hEq⟩
      rcases Prod.mk.inj hEq with ⟨rfl, rfl⟩
      have ⟨hL, hR⟩ := ih hDec
      simp only [tmNodeCount, stepCertSize]
      omega
  | congPairSnd fst code ih =>
      simp only [StepCode.decode, mapEndpoints, Option.map_eq_some_iff] at decoded
      rcases decoded with ⟨⟨l₀, r₀⟩, hDec, hEq⟩
      rcases Prod.mk.inj hEq with ⟨rfl, rfl⟩
      have ⟨hL, hR⟩ := ih hDec
      simp only [tmNodeCount, stepCertSize]
      omega
  | congFst code ih =>
      simp only [StepCode.decode, mapEndpoints, Option.map_eq_some_iff] at decoded
      rcases decoded with ⟨⟨l₀, r₀⟩, hDec, hEq⟩
      rcases Prod.mk.inj hEq with ⟨rfl, rfl⟩
      have ⟨hL, hR⟩ := ih hDec
      simp only [tmNodeCount, stepCertSize]
      omega
  | congSnd code ih =>
      simp only [StepCode.decode, mapEndpoints, Option.map_eq_some_iff] at decoded
      rcases decoded with ⟨⟨l₀, r₀⟩, hDec, hEq⟩
      rcases Prod.mk.inj hEq with ⟨rfl, rfl⟩
      have ⟨hL, hR⟩ := ih hDec
      simp only [tmNodeCount, stepCertSize]
      omega
  | congRefl code ih =>
      simp only [StepCode.decode, mapEndpoints, Option.map_eq_some_iff] at decoded
      rcases decoded with ⟨⟨l₀, r₀⟩, hDec, hEq⟩
      rcases Prod.mk.inj hEq with ⟨rfl, rfl⟩
      have ⟨hL, hR⟩ := ih hDec
      simp only [tmNodeCount, stepCertSize]
      omega

/-- **Endpoint Lower Bound for Explicit Conversion Certificates**:
Every accepted `StructuralConversionCode.Code` between `left` and `right` has
certificate size at least `tmNodeCount left` and at least `tmNodeCount right`. -/
theorem codeCertSize_ge_endpoints [DecidableEq Head]
    {headEq : Head → Head → Prop} [DecidableRel headEq]
    {n : Nat} (code : Code Head (fun _ => Empty) n)
    {left right : Tm Head n}
    (decoded :
      code.decode headEq (RootDecoder.ofEmpty RootComputation.empty rfl).decode =
        some (left, right)) :
    tmNodeCount left ≤ codeCertSize (fun c => nomatch c) code ∧
      tmNodeCount right ≤ codeCertSize (fun c => nomatch c) code := by
  induction code generalizing left right with
  | single step =>
      exact stepCertSize_ge_endpoints step decoded
  | refl term =>
      simp only [Code.decode, Option.some.injEq, Prod.mk.injEq] at decoded
      rcases decoded with ⟨rfl, rfl⟩
      exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | symm code ih =>
      simp only [Code.decode, reverseEndpoints, Option.map_eq_some_iff] at decoded
      rcases decoded with ⟨⟨l₀, r₀⟩, hDec, hEq⟩
      rcases Prod.mk.inj hEq with ⟨rfl, rfl⟩
      have ⟨hL, hR⟩ := ih hDec
      exact ⟨hR, hL⟩
  | trans first second ihFirst ihSecond =>
      simp only [Code.decode, joinEndpoints] at decoded
      cases h1 : first.decode headEq (RootDecoder.ofEmpty RootComputation.empty rfl).decode with
      | none => simp [h1] at decoded
      | some p1 =>
          rcases p1 with ⟨l1, m1⟩
          cases h2 : second.decode headEq (RootDecoder.ofEmpty RootComputation.empty rfl).decode with
          | none => simp [h1, h2] at decoded
          | some p2 =>
              rcases p2 with ⟨m2, r2⟩
              simp only [h1, h2] at decoded
              split at decoded
              · simp only [Option.some.injEq, Prod.mk.injEq] at decoded
                rcases decoded with ⟨rfl, rfl⟩
                have ⟨hL1, _⟩ := ihFirst h1
                have ⟨_, hR2⟩ := ihSecond h2
                simp only [codeCertSize]
                omega
              · cases decoded

/-- Every decoded conversion certificate for non-identical terms `left ≠ right`
must have `1 ≤ code.stepCount`. -/
theorem stepCount_pos_of_decode_ne [DecidableEq Head]
    {headEq : Head → Head → Prop} [DecidableRel headEq]
    {n : Nat} {RootCode : Nat → Type}
    {decodeRoot : {m : Nat} → RootCode m → Option (Tm Head m × Tm Head m)}
    (code : Code Head RootCode n) {left right : Tm Head n}
    (decoded : code.decode headEq decodeRoot = some (left, right))
    (hne : left ≠ right) :
    1 ≤ code.stepCount := by
  induction code generalizing left right with
  | single _ => exact Nat.le_refl 1
  | refl term =>
      simp only [Code.decode, Option.some.injEq, Prod.mk.injEq] at decoded
      rcases decoded with ⟨rfl, rfl⟩
      exact False.elim (hne rfl)
  | symm c ih =>
      simp only [Code.decode, reverseEndpoints, Option.map_eq_some_iff] at decoded
      rcases decoded with ⟨⟨a, b⟩, hDec, hEq⟩
      rcases Prod.mk.inj hEq with ⟨rfl, rfl⟩
      exact ih hDec (Ne.symm hne)
  | trans c₁ c₂ ih₁ ih₂ =>
      simp only [Code.decode, joinEndpoints] at decoded
      cases h1 : c₁.decode headEq decodeRoot with
      | none => simp [h1] at decoded
      | some p1 =>
          rcases p1 with ⟨l1, m1⟩
          cases h2 : c₂.decode headEq decodeRoot with
          | none => simp [h1, h2] at decoded
          | some p2 =>
              rcases p2 with ⟨m2, r2⟩
              simp only [h1, h2] at decoded
              split at decoded
              · rename_i hMid
                subst hMid
                simp only [Option.some.injEq, Prod.mk.injEq] at decoded
                rcases decoded with ⟨rfl, rfl⟩
                by_cases hLM : l1 = m1
                · subst hLM
                  have h2Pos := ih₂ h2 hne
                  simp only [Code.stepCount]
                  omega
                · have h1Pos := ih₁ h1 hLM
                  simp only [Code.stepCount]
                  omega
              · cases decoded

/-- Every accepted conversion certificate for non-identical terms `left ≠ right`
must have `1 ≤ code.stepCount`. -/
theorem stepCount_pos_of_ne [DecidableEq Head]
    {headEq : Head → Head → Prop} [DecidableRel headEq]
    {n : Nat} {RootCode : Nat → Type}
    {decodeRoot : {m : Nat} → RootCode m → Option (Tm Head m × Tm Head m)}
    (code : Code Head RootCode n) {left right : Tm Head n}
    (checked : code.check headEq decodeRoot left right = true)
    (hne : left ≠ right) :
    1 ≤ code.stepCount :=
  stepCount_pos_of_decode_ne code (of_decide_eq_true checked) hne

/-- An $N$-step nested $\beta$-redex chain applying the identity `λ x. x` $N$ times to `base`. -/
def idBetaChain {n : Nat} (steps : Nat) (base : Tm Head n) : Tm Head n :=
  match steps with
  | 0 => base
  | k + 1 => .app (.lam (.var 0)) (idBetaChain k base)

/-- The syntactic node count of `idBetaChain steps base` is `3 * steps + tmNodeCount base`. -/
@[simp] theorem tmNodeCount_idBetaChain {n : Nat} (steps : Nat) (base : Tm Head n) :
    tmNodeCount (idBetaChain steps base) = 3 * steps + tmNodeCount base := by
  induction steps with
  | zero => simp [idBetaChain]
  | succ k ih =>
      simp only [idBetaChain, tmNodeCount, ih]
      omega

/-- Explicit `StructuralConversionCode.Code` witnessing `idBetaChain steps base ≡ base`. -/
def idBetaChainCode {RootCode : Nat → Type} {n : Nat} :
    (steps : Nat) → (base : Tm Head n) → Code Head RootCode n
  | 0, base => .refl base
  | k + 1, base =>
      .trans (.single (.betaPi (.var 0) (idBetaChain k base))) (idBetaChainCode k base)

theorem idBetaChainCode_check [DecidableEq Head]
    (headEq : Head → Head → Prop) [DecidableRel headEq]
    {RootCode : Nat → Type}
    (decodeRoot : {m : Nat} → RootCode m → Option (Tm Head m × Tm Head m))
    {n : Nat} (steps : Nat) (base : Tm Head n) :
    (idBetaChainCode steps base).check headEq decodeRoot
      (idBetaChain steps base) base = true := by
  induction steps with
  | zero =>
      simp [idBetaChain, idBetaChainCode, Code.check, Code.decode]
  | succ k ih =>
      have hDec : (idBetaChainCode k base).decode headEq decodeRoot =
          some (idBetaChain k base, base) := of_decide_eq_true ih
      have hInst : inst0 (idBetaChain k base) (.var 0 : Tm Head (n + 1)) =
          idBetaChain k base := rfl
      simp [idBetaChain, idBetaChainCode, Code.check, Code.decode, StepCode.decode,
        joinEndpoints, hDec, hInst]

/-- Therefore `idBetaChain steps base` is convertible to `base` in `Conv`. -/
theorem idBetaChain_conv [DecidableEq Head]
    (headEq : Head → Head → Prop) [DecidableRel headEq]
    {n : Nat} (steps : Nat) (base : Tm Head n) :
    Conv headEq (idBetaChain steps base) base RootComputation.empty := by
  exact Code.check_sound (RootDecoder.ofEmpty RootComputation.empty rfl)
    (idBetaChainCode_check headEq
      (RootDecoder.ofEmpty RootComputation.empty rfl).decode steps base)

/-- Explicit `SizedChecker` for conversion claims in `ParameterizedPiSigmaId` with
empty root computation, measuring each explicit `Code` by `codeCertSize`. -/
def explicitConversionSizedChecker [DecidableEq Head]
    (headEq : Head → Head → Prop) [DecidableRel headEq] (n : Nat) :
    SizedChecker (ConversionClaim (Tm Head n)) (Code Head (fun _ => Empty) n) where
  check claim code :=
    code.check headEq (RootDecoder.ofEmpty RootComputation.empty rfl).decode
      claim.source claim.target
  claimSize claim := tmNodeCount claim.source + tmNodeCount claim.target
  certificateSize := codeCertSize (fun c => nomatch c)

/-- Every accepted explicit conversion certificate for
`⟨idBetaChain steps base, base⟩` has size at least `3 * steps + tmNodeCount base`. -/
theorem explicitConversion_certSize_lower_bound [DecidableEq Head]
    (headEq : Head → Head → Prop) [DecidableRel headEq]
    {n : Nat} (steps : Nat) (base : Tm Head n)
    (code : Code Head (fun _ => Empty) n)
    (accepted :
      (explicitConversionSizedChecker headEq n).check
        ⟨idBetaChain steps base, base⟩ code = true) :
    3 * steps + tmNodeCount base ≤
      (explicitConversionSizedChecker headEq n).certificateSize code := by
  have decoded :
      code.decode headEq (RootDecoder.ofEmpty RootComputation.empty rfl).decode =
        some (idBetaChain steps base, base) :=
    of_decide_eq_true accepted
  have ⟨hLeft, _⟩ := codeCertSize_ge_endpoints code decoded
  simpa [explicitConversionSizedChecker, tmNodeCount_idBetaChain] using hLeft

/-- One-step recurrence for the syntactic size of the step-by-step explicit trace
`idBetaChainCode (k + 1) base`. Because each `.betaPi` step certificate records
both the argument `idBetaChain k base` and its instantiated reduct `idBetaChain k base`,
step `k + 1` adds `6 * k + 2 * tmNodeCount base + 3` nodes. -/
theorem codeCertSize_idBetaChainCode_succ {RootCode : Nat → Type}
    (rootSize : {m : Nat} → RootCode m → Nat)
    {n : Nat} (k : Nat) (base : Tm Head n) :
    codeCertSize rootSize (idBetaChainCode (RootCode := RootCode) (k + 1) base) =
      (6 * k + 2 * tmNodeCount base + 3) +
        codeCertSize rootSize (idBetaChainCode (RootCode := RootCode) k base) := by
  have hInst : inst0 (idBetaChain k base) (.var 0 : Tm Head (n + 1)) =
      idBetaChain k base := rfl
  simp only [idBetaChainCode, codeCertSize, stepCertSize, hInst,
    tmNodeCount, tmNodeCount_idBetaChain]
  omega

/-- **Exact Quadratic Size of the Step-by-Step Explicit Trace `idBetaChainCode`**:
Unfolding an $N$-step $\beta$-chain step by step in `StructuralConversionCode.Code`
materializes every intermediate term `idBetaChain k base` for $0 \le k < N$, giving
exact quadratic certificate size:
`2 * codeCertSize _ (idBetaChainCode steps base) = 6 * steps * (steps - 1) + 2 * steps * (2 * tmNodeCount base + 3) + 2 * tmNodeCount base`. -/
theorem codeCertSize_idBetaChainCode_quadratic {RootCode : Nat → Type}
    (rootSize : {m : Nat} → RootCode m → Nat)
    {n : Nat} (steps : Nat) (base : Tm Head n) :
    2 * codeCertSize rootSize (idBetaChainCode (RootCode := RootCode) steps base) =
      6 * steps * (steps - 1) +
        2 * steps * (2 * tmNodeCount base + 3) +
        2 * tmNodeCount base := by
  induction steps with
  | zero =>
      simp [idBetaChainCode, codeCertSize]
  | succ k ih =>
      rw [codeCertSize_idBetaChainCode_succ, Nat.mul_add, ih]
      cases k with
      | zero =>
          simp
      | succ m =>
          have hSub1 : m + 1 + 1 - 1 = m + 1 := rfl
          have hSub2 : m + 1 - 1 = m := rfl
          rw [hSub1, hSub2]
          ring

/-- Lower bound corollary: the step-by-step explicit trace `idBetaChainCode steps base`
has certificate size at least `3 * steps * (steps - 1) + tmNodeCount base`. -/
theorem codeCertSize_idBetaChainCode_ge_quadratic {RootCode : Nat → Type}
    (rootSize : {m : Nat} → RootCode m → Nat)
    {n : Nat} (steps : Nat) (base : Tm Head n) :
    3 * steps * (steps - 1) + tmNodeCount base ≤
      codeCertSize rootSize (idBetaChainCode (RootCode := RootCode) steps base) := by
  have hQuad := codeCertSize_idBetaChainCode_quadratic (RootCode := RootCode) rootSize steps base
  have hMul : 6 * steps * (steps - 1) = 2 * (3 * steps * (steps - 1)) := by ring
  omega

/-- **Exact Instrumented Step Count of the Closure Machine on `idBetaChain`**:
Evaluating `idBetaChain steps base` in our closure-based weak-head machine `whEvalSteps`
at fuel `fuel + 2 * steps` takes **exactly `3 * steps`** steps plus the steps to
evaluate `base` at `fuel`, independent of the syntactic size of `base` (because closures
bind arguments in $O(1)$ without eager substitution). -/
theorem whEvalSteps_idBetaChain (R : Rules Head)
    (root : TypedEquality.Normalization.ExecutableReduction.RootEvaluator R)
    {m n : Nat} (steps : Nat) (fuel : Nat) (env : WhEnv Head m n) (base : Tm Head m) :
    whEvalSteps R root (fuel + 2 * steps) env (idBetaChain steps base) =
      (whEvalSteps R root fuel env base).map (fun s => 3 * steps + s) := by
  induction steps with
  | zero =>
      simp only [idBetaChain, Nat.mul_zero, Nat.add_zero, Nat.zero_add]
      cases whEvalSteps R root fuel env base <;> rfl
  | succ k ih =>
      have hFuel : fuel + 2 * (k + 1) = (fuel + 2 * k) + 2 := by omega
      rw [hFuel]
      simp only [idBetaChain]
      rw [whEvalSteps_app_id R root (fuel + 2 * k) env (idBetaChain k base), ih]
      cases whEvalSteps R root fuel env base with
      | none => rfl
      | some s =>
          simp only [Option.map]
          congr 1
          omega

/-- Evaluating a $\Pi$-type `.pi A B` to weak-head normal form with empty root rules
takes `1` step (the closure machine stops immediately at a type former without
traversing `A` or `B`). -/
@[simp] theorem whEvalSteps_pi (R : Rules Head) {fuel m n : Nat}
    (env : WhEnv Head m n) (A : Tm Head m) (B : Tm Head (m + 1)) :
    whEvalSteps R (fun _ => none) (fuel + 1) env (.pi A B) = some 1 := rfl

/-- **Linear Step Count of `nbeWhnfSteps` on `idBetaChain steps (.pi A B)`**:
At fuel `2 * steps + 1`, our instrumented closure-based weak-head machine `nbeWhnfSteps`
evaluates `idBetaChain steps (.pi A B)` in **exactly `3 * steps + 1` recursive calls**,
completely independent of `tmNodeCount A` and `tmNodeCount B`. -/
theorem nbeWhnfSteps_idBetaChain_pi (R : Rules Head)
    {n : Nat} (steps : Nat) (A : Tm Head n) (B : Tm Head (n + 1)) :
    nbeWhnfSteps R (fun _ => none) (2 * steps + 1) (idBetaChain steps (.pi A B)) =
      some (3 * steps + 1) := by
  unfold nbeWhnfSteps
  have hFuel : 2 * steps + 1 = 1 + 2 * steps := by omega
  rw [hFuel, whEvalSteps_idBetaChain R (fun _ => none) steps 1 (WhEnv.idEnv n) (.pi A B)]
  rfl

/-- **Instrumented Step-Cost Separation Theorem Instantiating `TierLattice.not_traceBounded_of_fast`**:
When the verified conversion `DecisionKernel` is charged its **actual instrumented
closure-machine step count**
`decideTime claim := (nbeWhnfSteps R (fun _ => none) (2 * steps + 1) claim.source).getD 0`
(rather than a constant `1`), evaluating `idBetaChain steps (.pi A B)` costs
`3 * steps + 1` steps, whereas **every** accepted explicit conversion certificate
`code : Code Head (fun _ => Empty) n` for `⟨idBetaChain steps (.pi A B), .pi A B⟩`
has syntactic size `≥ 3 * steps + 1 + tmNodeCount A + tmNodeCount B ≥ 3 * steps + 3 > 3 * steps + 1`
(with gap `tmNodeCount A + tmNodeCount B ≥ 2`, growing arbitrarily with `|A| + |B|`,
and quadratic `3 * steps * (steps - 1)` for step-by-step traces `idBetaChainCode`).
By `TierLattice.not_traceBounded_of_fast`, no elaboration from the instrumented
verified conversion rung to explicit `StructuralConversionCode` certificates is
`TraceBounded`. -/
theorem verifiedRung_not_traceBounded_of_nbeWhnfSteps [DecidableEq Head]
    (R : Rules Head) [DecidableRel R.headEq]
    {n : Nat}
    (kernel :
      DecisionKernel (ConversionClaim (Tm Head n))
        (fun claim => Conv R.headEq claim.source claim.target RootComputation.empty))
    (steps : Nat) (A : Tm Head n) (B : Tm Head (n + 1))
    (elaboration :
      Elaboration
        (decisionTimed kernel
          (fun c => tmNodeCount c.source + tmNodeCount c.target)
          (fun c => (nbeWhnfSteps R (fun _ => none) (2 * steps + 1) c.source).getD 0)).toChecker
        (explicitConversionSizedChecker R.headEq n).toChecker) :
    ¬ Elaboration.TraceBounded
        (computing :=
          decisionTimed kernel
            (fun c => tmNodeCount c.source + tmNodeCount c.target)
            (fun c => (nbeWhnfSteps R (fun _ => none) (2 * steps + 1) c.source).getD 0))
        (explicit := explicitConversionSizedChecker R.headEq n)
        elaboration := by
  let base : Tm Head n := .pi A B
  have hConv :
      Conv R.headEq (idBetaChain steps base) base RootComputation.empty :=
    idBetaChain_conv R.headEq steps base
  have hAccepted :
      (decisionTimed kernel
        (fun c => tmNodeCount c.source + tmNodeCount c.target)
        (fun c => (nbeWhnfSteps R (fun _ => none) (2 * steps + 1) c.source).getD 0)).check
          ⟨idBetaChain steps base, base⟩ () = true := by
    change kernel.decide ⟨idBetaChain steps base, base⟩ = true
    exact (kernel.correct ⟨idBetaChain steps base, base⟩).mpr hConv
  refine not_traceBounded_of_fast
    (computing :=
      decisionTimed kernel
        (fun c => tmNodeCount c.source + tmNodeCount c.target)
        (fun c => (nbeWhnfSteps R (fun _ => none) (2 * steps + 1) c.source).getD 0))
    (explicit := explicitConversionSizedChecker R.headEq n)
    elaboration hAccepted ?_
  intro elaborated explicitAccepted
  have hLower :=
    explicitConversion_certSize_lower_bound R.headEq steps base elaborated explicitAccepted
  have hStepsEq :
      (nbeWhnfSteps R (fun _ => none) (2 * steps + 1) (idBetaChain steps base)).getD 0 =
        3 * steps + 1 := by
    rw [nbeWhnfSteps_idBetaChain_pi R steps A B]
    rfl
  have hAPos : 1 ≤ tmNodeCount A := tmNodeCount_pos A
  have hBPos : 1 ≤ tmNodeCount B := tmNodeCount_pos B
  have hBaseSize : tmNodeCount base = 1 + tmNodeCount A + tmNodeCount B := rfl
  change (nbeWhnfSteps R (fun _ => none) (2 * steps + 1) (idBetaChain steps base)).getD 0 <
    (explicitConversionSizedChecker R.headEq n).certificateSize elaborated
  omega

/-- Unit-cost corollary (`decideTime := fun _ => 1`) when `1 ≤ steps`. -/
theorem verifiedRung_not_traceBounded_of_idBetaChain [DecidableEq Head]
    (headEq : Head → Head → Prop) [DecidableRel headEq]
    {n : Nat}
    (kernel :
      DecisionKernel (ConversionClaim (Tm Head n))
        (fun claim => Conv headEq claim.source claim.target RootComputation.empty))
    (steps : Nat) (hSteps : 1 ≤ steps) (base : Tm Head n)
    (elaboration :
      Elaboration
        (decisionTimed kernel
          (fun c => tmNodeCount c.source + tmNodeCount c.target)
          (fun _ => 1)).toChecker
        (explicitConversionSizedChecker headEq n).toChecker) :
    ¬ Elaboration.TraceBounded
        (computing :=
          decisionTimed kernel
            (fun c => tmNodeCount c.source + tmNodeCount c.target)
            (fun _ => 1))
        (explicit := explicitConversionSizedChecker headEq n)
        elaboration := by
  have hConv :
      Conv headEq (idBetaChain steps base) base RootComputation.empty :=
    idBetaChain_conv headEq steps base
  have hAccepted :
      (decisionTimed kernel
        (fun c => tmNodeCount c.source + tmNodeCount c.target)
        (fun _ => 1)).check ⟨idBetaChain steps base, base⟩ () = true := by
    change kernel.decide ⟨idBetaChain steps base, base⟩ = true
    exact (kernel.correct ⟨idBetaChain steps base, base⟩).mpr hConv
  refine not_traceBounded_of_fast
    (computing :=
      decisionTimed kernel
        (fun c => tmNodeCount c.source + tmNodeCount c.target)
        (fun _ => 1))
    (explicit := explicitConversionSizedChecker headEq n)
    elaboration hAccepted ?_
  intro elaborated explicitAccepted
  have hLower :=
    explicitConversion_certSize_lower_bound headEq steps base elaborated explicitAccepted
  have hBasePos : 1 ≤ tmNodeCount base := tmNodeCount_pos base
  change 1 < (explicitConversionSizedChecker headEq n).certificateSize elaborated
  omega

end Separation

/-! ## 4. Instantiation: `Legacy` inside `Tower` as a Fibered Bubble Carve-Out -/

namespace LegacyBubble

/-- Free-variable dependency set as an operational-step-invariant observation on
scoped terms (`Tm.freeVariables` depends only on bound/free indices, or we can
observe syntactic scope arity / closedness). For an observation invariant under
all `Step Legacy.HeadEq` reductions, we observe the ambient scope size `n` and
whether the term is in a closed context (`decide (n = 0)`). -/
structure ScopeObservation where
  arity : Nat
  isClosedScope : Bool
  deriving DecidableEq, Repr

def observeLegacy {n : Nat} (_t : Legacy.Tm n) : ScopeObservation :=
  ⟨n, decide (n = 0)⟩

def observeTower {n : Nat} (_t : Tower.Tm n) : ScopeObservation :=
  ⟨n, decide (n = 0)⟩

@[simp] theorem observeTower_embed {n : Nat} (t : Legacy.Tm n) :
    observeTower (Legacy.embed t) = observeLegacy t := rfl

/-- Typing judgment triple `(Γ, t, A)` for `Legacy` and `Tower` at scope `n`. -/
structure LegacyTypingClaim (n : Nat) where
  ctx : Legacy.Ctx n
  term : Legacy.Tm n
  type : Legacy.Tm n

structure TowerTypingClaim (n : Nat) where
  ctx : Tower.Ctx n
  term : Tower.Tm n
  type : Tower.Tm n

def embedTypingClaim {n : Nat} (c : LegacyTypingClaim n) : TowerTypingClaim n where
  ctx := Legacy.embedCtx c.ctx
  term := Legacy.embed c.term
  type := Legacy.embed c.type

/-- **Positive Instantiation of `FiberedBubble`**:
The one-universe `Legacy` presentation embeds into the carved-out `Tower.SealedHasType`
subjudgment of the cumulative `Tower` presentation, preserving and reflecting:
1. the typing judgment (`Legacy.hasType_iff_sealedHasType`),
2. one-step, multi-step, and symmetric-transitive computation (`Legacy.towerStep_of_step`,
   `Legacy.step_of_towerStep`), and
3. the scope observation interface. -/
def legacyInTowerBubble (n : Nat) :
    FiberedBubble (Legacy.Tm n) (Tower.Tm n)
      (LegacyTypingClaim n) (TowerTypingClaim n) ScopeObservation where
  embedTerm := Legacy.embed
  forgetTerm := Legacy.forget
  forget_embed := Legacy.forget_embed
  embedJudgment := embedTypingClaim
  bubbleDerivable c := Legacy.HasType c.ctx c.term c.type
  topDerivable c := Tower.SealedHasType c.ctx c.term c.type
  bubbleStep := Step Legacy.HeadEq
  topStep := Step Tower.HeadEq
  judgment_iff c := Legacy.hasType_iff_sealedHasType c.ctx c.term c.type
  step_to_top := Legacy.towerStep_of_step
  step_of_top := Legacy.step_of_towerStep
  bubbleObserve := observeLegacy
  topObserve := observeTower
  observe_commutes := observeTower_embed
  observe_step_invariant _ := rfl

/-- Corollary: `legacyInTowerBubble` preserves and reflects one-step computation. -/
theorem legacyInTower_step_iff {n : Nat} (x y : Legacy.Tm n) :
    Step Legacy.HeadEq x y ↔ Step Tower.HeadEq (Legacy.embed x) (Legacy.embed y) :=
  (legacyInTowerBubble n).step_iff x y

/-- Corollary: `legacyInTowerBubble` preserves and reflects multi-step reduction. -/
theorem legacyInTower_reduces_iff {n : Nat} (x y : Legacy.Tm n) :
    Relation.ReflTransGen (Step Legacy.HeadEq) x y ↔
      Relation.ReflTransGen (Step Tower.HeadEq) (Legacy.embed x) (Legacy.embed y) :=
  (legacyInTowerBubble n).reduces_iff x y

/-- Corollary: `legacyInTowerBubble` preserves and reflects conversion. -/
theorem legacyInTower_conv_iff {n : Nat} (x y : Legacy.Tm n) :
    Conv Legacy.HeadEq x y ↔ Conv Tower.HeadEq (Legacy.embed x) (Legacy.embed y) :=
  (legacyInTowerBubble n).conv_iff x y

/-- **Negative Control for Bubble Carve-Out**:
Attempting to use unrestricted `Tower.HasType` (which includes `U l : U (succ l)`)
instead of the carved-out `Tower.SealedHasType` fiber breaks judgment reflection
(`judgment_iff`): `Legacy.legacyUniverseLeak` is well-typed in `Tower.HasType`
after embedding, but is not typable in `Legacy.HasType`. -/
theorem unrestricted_tower_not_judgment_reflecting :
    ∃ (c : LegacyTypingClaim 0),
      Tower.HasType (embedTypingClaim c).ctx (embedTypingClaim c).term (embedTypingClaim c).type ∧
        ¬ Legacy.HasType c.ctx c.term c.type :=
  ⟨⟨.nil, Legacy.legacyUniverseLeak, .head .marker⟩,
    Legacy.towerUniverseLeak_hasType,
    Legacy.legacyUniverseLeak_not_hasType⟩

end LegacyBubble

end Mettapedia.TypeTheory.NbE
