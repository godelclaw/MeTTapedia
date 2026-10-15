import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Field.Rat
import Mathlib.Data.Rat.Defs
import Mettapedia.GSLT.Contexts.TermsAlone
import Mettapedia.Logic.HostingStyles.Weighted.SemiringTransport

/-!
# Hosting for the support of a kernel

`Hosting` is read on the theory whose rewrites are the support of one labelled
row. It does not decide weight preservation, and weight preservation does not
decide it. With a section of the read-back on successors of images,
preservation over a semiring without cancellation gives both transition laws;
over `OrBool`, with the read-back a retraction on source successors as well,
those laws give preservation back.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.Weighted

open Classical
open Mettapedia.GSLT
open Mettapedia.GSLT.Distinction.Probabilistic
open Mettapedia.GSLT.GradedSupport

/-! ## The theory of one support row -/

/-- **The GSLT whose rewrites are the support of one labelled row.** A step
lands on every term equated to a supported successor. -/
noncomputable def supportGSLT {S : GSLT} {K : Type*} [Semiring K]
    (W : WeightedSystem S K) (noCancel : NoCancellation K) (label : W.Label) : GSLT where
  Term := S.Term
  equations := S.equations
  rewrites source target := ∃ x ∈ (W.kernel label source).support, S.Equiv x target
  rewrites_resp_left := by
    intro source source' target equivalent ⟨x, member, close⟩
    have nonzero : closedSum (W.kernel label source) (fun y => S.Equiv y target) ≠ 0 :=
      (closedSum_ne_zero_iff noCancel _ _).mpr ⟨x, member, close⟩
    rw [W.kernel_resp label equivalent _ (ProbabilisticSystem.equiv_closed target)] at nonzero
    obtain ⟨x', member', close'⟩ := (closedSum_ne_zero_iff noCancel _ _).mp nonzero
    exact ⟨target, ⟨x', member', close'⟩, S.equations.iseqv.refl target⟩
  rewrites_resp_right := by
    intro _ _ target' ⟨x, member, close⟩ equivalent
    exact ⟨x, member, S.equations.iseqv.trans close equivalent⟩

theorem quiet_cases (term : quiet.Term) :
    term = none ∨ ∃ b : Bool, term = some b := by
  cases term with
  | none => exact Or.inl rfl
  | some b => exact Or.inr ⟨b, rfl⟩

/-- **Positive.** Weight `1` steps from the start to `some true`. -/
theorem outcome_one_rewrites_true :
    (supportGSLT (outcomeSystem (1 : ℕ)) nat_noCancellation ()).rewrites none (some true) :=
  ⟨some true,
    Finsupp.mem_support_iff.mpr ((outcomeSystem_coeff (1 : ℕ) true).symm ▸ Nat.one_ne_zero), rfl⟩

theorem outcome_zero_coeff (source target : quiet.Term) :
    (outcomeSystem (0 : ℕ)).kernel () source target = 0 := by
  rcases quiet_cases source with rfl | ⟨b, rfl⟩
  · rcases quiet_cases target with rfl | ⟨c, rfl⟩
    · show outcomeStep (0 : ℕ) none none = 0
      rw [outcomeStep, outcomeKernel, Finsupp.onFinset_apply]
      rfl
    · exact outcomeSystem_coeff 0 c
  · show outcomeStep (0 : ℕ) (some b) target = 0
    rfl

/-- **Negative.** Weight `0` has no support step. -/
theorem outcome_zero_no_rewrite (source target : quiet.Term) :
    ¬ (supportGSLT (outcomeSystem (0 : ℕ)) nat_noCancellation ()).rewrites source target := by
  intro ⟨x, member, _⟩
  exact (Finsupp.mem_support_iff).mp member (outcome_zero_coeff source x)

theorem no_rewrite_of_zero {S : GSLT} {K : Type*} [Semiring K]
    (W : WeightedSystem S K) (noCancel : NoCancellation K) (label : W.Label)
    (zero : ∀ source target, W.kernel label source target = 0) (source target : S.Term) :
    ¬ (supportGSLT W noCancel label).rewrites source target := by
  intro ⟨x, member, _⟩
  exact (Finsupp.mem_support_iff).mp member (zero source x)

/-- The terms-alone theory of one support row, and the map induced by `F`. -/
noncomputable def supportTheory {S : GSLT} {K : Type*} [Semiring K]
    (W : WeightedSystem S K) (noCancel : NoCancellation K) (label : W.Label) : ContextTheory :=
  (supportGSLT W noCancel label).termsAlone

noncomputable def supportOfTerms {sourceSpace targetSpace : GSLT} {K : Type*} [Semiring K]
    (map : KernelMap K sourceSpace targetSpace) (noCancel : NoCancellation K)
    (label : map.source.Label)
    (term_resp : ∀ {first second : sourceSpace.Term}, sourceSpace.Equiv first second →
      targetSpace.Equiv (map.term first) (map.term second)) :
    ContextMap (supportTheory map.source noCancel label)
      (supportTheory map.target noCancel (map.labelMap label)) :=
  ContextMap.ofTerms PUnit.unit map.term term_resp

theorem support_id_exhausting {S : GSLT} {K L : Type*} [Semiring K] [Semiring L]
    (sourceW : WeightedSystem S K) (targetW : WeightedSystem S L)
    (noCancelK : NoCancellation K) (noCancelL : NoCancellation L)
    (sourceLabel : sourceW.Label) (targetLabel : targetW.Label) :
    (ContextMap.ofTerms (source := supportGSLT sourceW noCancelK sourceLabel)
      (target := (supportGSLT targetW noCancelL targetLabel).termsAlone)
      PUnit.unit id (fun equivalent => equivalent)).Exhausting := by
  intro _ _ result observer
  refine ⟨observer, fun filling => ?_⟩
  have image := ContextMap.fill_termsImage (source := supportGSLT sourceW noCancelK sourceLabel)
    (target := (supportGSLT targetW noCancelL targetLabel).termsAlone)
    PUnit.unit id observer filling
  exact ContextMap.equations_of_eq (interface := result) image

theorem support_id_hosting_of_rewrites {S : GSLT} {K L : Type*} [Semiring K] [Semiring L]
    (sourceW : WeightedSystem S K) (targetW : WeightedSystem S L)
    (noCancelK : NoCancellation K) (noCancelL : NoCancellation L)
    (sourceLabel : sourceW.Label) (targetLabel : targetW.Label)
    (same : ∀ source target,
      (supportGSLT sourceW noCancelK sourceLabel).rewrites source target ↔
        (supportGSLT targetW noCancelL targetLabel).rewrites source target) :
    (ContextMap.ofTerms (source := supportGSLT sourceW noCancelK sourceLabel)
      (target := (supportGSLT targetW noCancelL targetLabel).termsAlone)
      PUnit.unit id (fun equivalent => equivalent)).Hosting := by
  refine (ContextMap.ofTerms_hosting_iff
      (source := supportGSLT sourceW noCancelK sourceLabel)
      (target := (supportGSLT targetW noCancelL targetLabel).termsAlone)
      PUnit.unit id (fun equivalent => equivalent)).mpr
    ⟨fun _ _ equivalent => equivalent, ?_, ?_⟩
  · intro first next step
    exact (same first next).mp step
  · intro first next step
    exact ⟨next, (same first next).mpr step,
      ((supportGSLT targetW noCancelL targetLabel).equations).iseqv.refl _⟩

/-! ## Factor `k`: hosting and exhausting, weights scaled -/

noncomputable def scaleMap : KernelMap ℕ quiet quiet where
  source := outcomeSystem 1
  target := outcomeSystem (2 * 1)
  term := id
  labelMap := id
  readBack := id
  readBack_resp := fun equivalent => equivalent

theorem outcome_support_iff {K : Type*} [CommSemiring K] (w : K) (noCancel : NoCancellation K)
    (source target : quiet.Term) :
    (supportGSLT (outcomeSystem w) noCancel ()).rewrites source target ↔
      w ≠ 0 ∧ source = none ∧ ∃ b : Bool, target = some b := by
  constructor
  · rintro ⟨x, member, equivalent⟩
    have nonzero : (outcomeSystem w).kernel () source x ≠ 0 :=
      (Finsupp.mem_support_iff).mp member
    rcases quiet_cases source with rfl | ⟨b, rfl⟩
    · rcases quiet_cases x with rfl | ⟨c, rfl⟩
      · exact absurd (by
          show outcomeStep w none none = 0
          rw [outcomeStep, outcomeKernel, Finsupp.onFinset_apply]
          rfl) nonzero
      · have weight : w ≠ 0 := by
          rw [outcomeSystem_coeff] at nonzero
          exact nonzero
        exact ⟨weight, rfl, c, equivalent.symm⟩
    · exact absurd (by
        show outcomeStep w (some b) x = 0
        rfl) nonzero
  · rintro ⟨weight, rfl, b, rfl⟩
    exact ⟨some b, Finsupp.mem_support_iff.mpr ((outcomeSystem_coeff w b).symm ▸ weight), rfl⟩

theorem scale_rewrites_iff (source target : quiet.Term) :
    (supportGSLT (outcomeSystem (1 : ℕ)) nat_noCancellation ()).rewrites source target ↔
      (supportGSLT (outcomeSystem (2 * 1 : ℕ)) nat_noCancellation ()).rewrites source target := by
  constructor
  · intro step
    rcases (outcome_support_iff (1 : ℕ) nat_noCancellation source target).mp step with
      ⟨_, start, hit⟩
    exact (outcome_support_iff (2 * 1 : ℕ) nat_noCancellation source target).mpr
      ⟨Nat.succ_ne_zero 1, start, hit⟩
  · intro step
    rcases (outcome_support_iff (2 * 1 : ℕ) nat_noCancellation source target).mp step with
      ⟨_, start, hit⟩
    exact (outcome_support_iff (1 : ℕ) nat_noCancellation source target).mpr
      ⟨Nat.one_ne_zero, start, hit⟩

/-- **(a) Hosting.** Doubling every weight keeps the support steps. -/
theorem scale_hosting :
    (ContextMap.ofTerms (source := supportGSLT (outcomeSystem (1 : ℕ)) nat_noCancellation ())
      (target := (supportGSLT (outcomeSystem (2 * 1 : ℕ)) nat_noCancellation ()).termsAlone)
      PUnit.unit id (fun equivalent => equivalent)).Hosting :=
  support_id_hosting_of_rewrites (outcomeSystem 1) (outcomeSystem (2 * 1))
    nat_noCancellation nat_noCancellation () () scale_rewrites_iff

/-- **(a) Exhausting.** The same identity hits every target context. -/
theorem scale_exhausting :
    (ContextMap.ofTerms (source := supportGSLT (outcomeSystem (1 : ℕ)) nat_noCancellation ())
      (target := (supportGSLT (outcomeSystem (2 * 1 : ℕ)) nat_noCancellation ()).termsAlone)
      PUnit.unit id (fun equivalent => equivalent)).Exhausting :=
  support_id_exhausting (outcomeSystem 1) (outcomeSystem (2 * 1))
    nat_noCancellation nat_noCancellation () ()

theorem scale_target_sum :
    closedSum ((outcomeSystem (2 * 1 : ℕ)).kernel () none) (fun t => t = some true) = 2 := by
  show closedSum (outcomeStep (2 * 1 : ℕ) none) (fun t => t = some true) = 2
  rw [outcomeStep, closedSum_outcomeKernel]
  simp

/-- **(a) Not weight-preserving.** The singleton `{some true}` sums to `1` on the
source and to `2` on the image. -/
theorem scale_not_preserving : ¬ KernelPreserving scaleMap := by
  intro preserves
  have eq := preserves () none (fun t => t = some true) quiet_true_closed
  have sourceSide :
      closedSum (scaleMap.source.kernel () none) (fun t => t = some true) = 1 :=
    closedSum_doubled_source
  have targetSide :
      closedSum (scaleMap.target.kernel (scaleMap.labelMap ()) (scaleMap.term none))
        (fun t => t = some true) = 2 := by
    have fold :
        closedSum (scaleMap.target.kernel (scaleMap.labelMap ()) (scaleMap.term none))
          (fun t => t = some true) =
          closedSum ((outcomeSystem (2 * 1 : ℕ)).kernel () none) (fun t => t = some true) := rfl
    exact fold.trans scale_target_sum
  exact absurd (sourceSide.symm.trans (eq.trans targetSide)) (by decide)

/-- **Diagonal, Hosting.** The identity on one support theory is hosting. -/
theorem identity_support_hosting :
    (ContextMap.ofTerms (source := supportGSLT (outcomeSystem (1 : ℕ)) nat_noCancellation ())
      (target := (supportGSLT (outcomeSystem (1 : ℕ)) nat_noCancellation ()).termsAlone)
      PUnit.unit id (fun equivalent => equivalent)).Hosting :=
  support_id_hosting_of_rewrites (outcomeSystem 1) (outcomeSystem 1)
    nat_noCancellation nat_noCancellation () () fun _ _ => Iff.rfl

/-- **Diagonal, Exhausting.** The identity on one support theory is exhausting. -/
theorem identity_support_exhausting :
    (ContextMap.ofTerms (source := supportGSLT (outcomeSystem (1 : ℕ)) nat_noCancellation ())
      (target := (supportGSLT (outcomeSystem (1 : ℕ)) nat_noCancellation ()).termsAlone)
      PUnit.unit id (fun equivalent => equivalent)).Exhausting :=
  support_id_exhausting (outcomeSystem 1) (outcomeSystem 1)
    nat_noCancellation nat_noCancellation () ()

/-! ## Hosting without exhausting -/

theorem fan_zero_coeff (source target : (fanSpace 2).Term) :
    (fanSystem 2 (0 : ℕ)).kernel () source target = 0 := by
  cases source with
  | none =>
    cases target with
    | none =>
      show fanStep 2 (0 : ℕ) none none = 0
      rw [fanStep, fanKernel, Finsupp.onFinset_apply]
      rfl
    | some q =>
      show fanStep 2 (0 : ℕ) none (some q) = 0
      exact fanKernel_some 2 (0 : ℕ) q
  | some p =>
    show fanStep 2 (0 : ℕ) (some p) target = 0
    rfl

noncomputable def deadEmbed : KernelMap ℕ quiet (fanSpace 2) where
  source := outcomeSystem 0
  target := fanSystem 2 0
  term := quietEmbed 2 (by decide)
  labelMap := id
  readBack := fanRead
  readBack_resp := by
    intro _ _ equivalent
    cases equivalent
    rfl

noncomputable def deadEmbedTerms : ContextMap (supportTheory (outcomeSystem (0 : ℕ)) nat_noCancellation ())
    (supportTheory (fanSystem 2 (0 : ℕ)) nat_noCancellation ()) :=
  supportOfTerms deadEmbed nat_noCancellation () (by
    intro _ _ equivalent
    cases equivalent
    rfl)

theorem quietEmbed_injective {k : ℕ} (hk : 0 < k) {first second : quiet.Term}
    (same : quietEmbed k hk first = quietEmbed k hk second) : first = second := by
  rcases quiet_cases first with rfl | ⟨b, rfl⟩
  · rcases quiet_cases second with rfl | ⟨c, rfl⟩
    · rfl
    · cases same
  · rcases quiet_cases second with rfl | ⟨c, rfl⟩
    · cases same
    · have pair := Option.some_injective _ same
      exact congrArg some (congrArg Prod.fst pair)

theorem quietEmbed_misses (term : quiet.Term) :
    quietEmbed 2 (by decide) term ≠ some (true, (1 : Fin 2)) := by
  intro same
  rcases quiet_cases term with rfl | ⟨b, rfl⟩
  · cases same
  · have pair := Option.some_injective _ same
    exact Nat.zero_ne_one (congrArg Fin.val (congrArg Prod.snd pair))

/-- **Hosting does not give Exhausting.** The dead embedding is faithful and has
no steps to preserve or reflect, and `some (true, 1)` is not an image. -/
theorem deadEmbed_hosting : deadEmbedTerms.Hosting := by
  refine (ContextMap.ofTerms_hosting_iff
    (source := supportGSLT (outcomeSystem (0 : ℕ)) nat_noCancellation ())
    (target := (supportGSLT (fanSystem 2 (0 : ℕ)) nat_noCancellation ()).termsAlone)
    PUnit.unit deadEmbed.term (by
      intro _ _ equivalent
      cases equivalent
      rfl)).mpr ⟨?_, ?_, ?_⟩
  · intro first second same
    exact quietEmbed_injective (by decide) same
  · intro first next step
    exact (outcome_zero_no_rewrite first next step).elim
  · intro first next step
    exact (no_rewrite_of_zero (fanSystem 2 0) nat_noCancellation () fan_zero_coeff
      (deadEmbed.term first) next step).elim

theorem deadEmbed_not_exhausting : ¬ deadEmbedTerms.Exhausting := by
  intro exhausting
  obtain ⟨preimage, identified⟩ :=
    ContextMap.Exhausting.term_surjective (map := deadEmbedTerms) exhausting
      (origin := PUnit.unit) (some (true, (1 : Fin 2)))
  exact quietEmbed_misses preimage identified.symm

/-! ## Exhausting without hosting -/

def collapseTerms : ContextMap (GSLT.stepFree Bool).termsAlone (GSLT.stepFree Unit).termsAlone :=
  ContextMap.ofTerms PUnit.unit (fun _ => ()) (fun _ => rfl)

theorem collapse_exhausting : collapseTerms.Exhausting := by
  intro _ _ result observer
  cases observer with
  | hole position only =>
    refine ⟨TermsContext.hole position only, fun filling => ?_⟩
    have image := ContextMap.fill_termsImage (source := GSLT.stepFree Bool)
      (target := (GSLT.stepFree Unit).termsAlone) PUnit.unit (fun _ : (GSLT.stepFree Bool).Term => ())
      (TermsContext.hole position only) filling
    exact ContextMap.equations_of_eq image
  | constant term empty =>
    refine ⟨TermsContext.constant (true : (GSLT.stepFree Bool).Term) empty, fun filling => ?_⟩
    have image := ContextMap.fill_termsImage (source := GSLT.stepFree Bool)
      (target := (GSLT.stepFree Unit).termsAlone) PUnit.unit (fun _ : (GSLT.stepFree Bool).Term => ())
      (TermsContext.constant (true : (GSLT.stepFree Bool).Term) empty) filling
    exact ContextMap.equations_of_eq (image.trans (congrArg id (Unit.eq_unit term)))

/-- **Exhausting does not give Hosting.** Collapsing `Bool` onto `Unit` hits
every target context and identifies two inequivalent terms. -/
theorem collapse_not_hosting : ¬ collapseTerms.Hosting :=
  ContextMap.not_hosting_of_identifies (map := collapseTerms) (origin := PUnit.unit)
    (first := true) (second := false) (by
      intro same
      have equal : (true : (GSLT.stepFree Bool).Term) = false := same
      cases equal) rfl

/-! ## The rationals cancel, so the divided fan uses nonnegative rationals -/

/-- Opposite weights on the two outcomes. -/
def cancelCoeff : Option Bool → ℚ
  | none => 0
  | some true => 1
  | some false => -1

/-- **A rational row that cancels.** Weight `1` on `some true` and `-1` on `some false`. -/
noncomputable def cancelPair : Option Bool →₀ ℚ :=
  Finsupp.onFinset {some true, some false} cancelCoeff fun term nonzero => by
    cases term with
    | none => exact absurd rfl nonzero
    | some b =>
      cases b
      · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      · exact Finset.mem_insert_self _ _

/-- **Positive coefficient.** The true outcome still carries weight `1`. -/
theorem cancelPair_true : cancelPair (some true) = 1 := by
  unfold cancelPair
  rw [Finsupp.onFinset_apply]
  rfl

/-- **The closed sum vanishes.** The two opposite weights add to `0`. -/
theorem cancelPair_sum : closedSum cancelPair (fun _ : Option Bool => True) = 0 := by
  unfold cancelPair
  rw [closedSum_onFinset]
  have pair : ({some true, some false} : Finset (Option Bool)) =
      insert (some true) {some false} := by
    ext x
    simp
  rw [pair, Finset.sum_insert (by decide), Finset.sum_singleton]
  simp [cancelCoeff]

/-- The row is supported at `some true` and its closed sum on every outcome is `0`. -/
theorem rat_row_cancels :
    closedSum cancelPair (fun _ : Option Bool => True) = 0 ∧ cancelPair (some true) ≠ 0 :=
  ⟨cancelPair_sum, cancelPair_true.symm ▸ one_ne_zero⟩

/-- **`ℚ` has no `NoCancellation`.** A supported coefficient and a zero closed sum
cannot coexist when sums of zero have zero summands. The divided fan below is
therefore stated on `ℚ≥0`. -/
theorem rat_not_noCancellation : ¬ NoCancellation ℚ := by
  intro law
  have nonzero : cancelPair (some true) ≠ 0 := rat_row_cancels.2
  have member : some true ∈ cancelPair.support := Finsupp.mem_support_iff.mpr nonzero
  exact ((closedSum_ne_zero_iff law cancelPair (fun _ : Option Bool => True)).mpr
    ⟨some true, member, trivial⟩) rat_row_cancels.1

/-! ## Divided fan: preserving, not hosting -/

noncomputable def dividedFan : KernelMap ℚ≥0 quiet (fanSpace 2) where
  source := outcomeSystem 1
  target := fanSystem 2 (1 / 2)
  term := quietEmbed 2 (by decide)
  labelMap := id
  readBack := fanRead
  readBack_resp := by
    intro _ _ equivalent
    cases equivalent
    rfl

theorem halves_of_bool (hit : Prop) :
    (if hit then (1 / 2 : ℚ≥0) else 0) + (if hit then (1 / 2 : ℚ≥0) else 0) =
      if hit then 1 else 0 := by
  by_cases holds : hit
  · simp only [if_pos holds]
    simpa using add_halves (1 : ℚ≥0)
  · simp only [if_neg holds, add_zero]

theorem sum_four {K : Type*} [AddCommMonoid K] (f : Bool × Fin 2 → K) :
    (∑ p : Bool × Fin 2, f p) =
      f (true, 0) + (f (true, 1) + (f (false, 0) + f (false, 1))) := by
  have carriers : (Finset.univ : Finset (Bool × Fin 2)) =
      insert (true, 0) (insert (true, 1) (insert (false, 0) {(false, 1)})) := by
    decide
  rw [carriers, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]

theorem fan_pair_sum (C : quiet.Term → Prop) :
    (∑ p : Bool × Fin 2, if C (fanRead (some p)) then (1 / 2 : ℚ≥0) else 0) =
      (if C (some true) then 1 else 0) + (if C (some false) then 1 else 0) := by
  refine (sum_four (fun p => if C (fanRead (some p)) then (1 / 2 : ℚ≥0) else 0)).trans ?_
  have trueHalf := halves_of_bool (C (some true))
  have falseHalf := halves_of_bool (C (some false))
  calc
    (if C (fanRead (some (true, (0 : Fin 2)))) then (1 / 2 : ℚ≥0) else 0) +
        ((if C (fanRead (some (true, 1))) then (1 / 2 : ℚ≥0) else 0) +
          ((if C (fanRead (some (false, 0))) then (1 / 2 : ℚ≥0) else 0) +
            if C (fanRead (some (false, 1))) then (1 / 2 : ℚ≥0) else 0)) =
        (if C (some true) then (1 / 2 : ℚ≥0) else 0) +
          ((if C (some true) then (1 / 2 : ℚ≥0) else 0) +
            ((if C (some false) then (1 / 2 : ℚ≥0) else 0) +
              if C (some false) then (1 / 2 : ℚ≥0) else 0)) := by
      simp only [fanRead_some]
    _ = ((if C (some true) then (1 / 2 : ℚ≥0) else 0) +
          if C (some true) then (1 / 2 : ℚ≥0) else 0) +
        ((if C (some false) then (1 / 2 : ℚ≥0) else 0) +
          if C (some false) then (1 / 2 : ℚ≥0) else 0) := by
      rw [add_assoc]
    _ = (if C (some true) then 1 else 0) + (if C (some false) then 1 else 0) := by
      rw [trueHalf, falseHalf]

theorem divided_source_sum (C : quiet.Term → Prop) :
    closedSum ((outcomeSystem (1 : ℚ≥0)).kernel () none) C =
      (if C (some true) then 1 else 0) + (if C (some false) then 1 else 0) :=
  closedSum_outcomeKernel (1 : ℚ≥0) C

theorem divided_target_sum (C : quiet.Term → Prop) :
    closedSum ((fanSystem 2 (1 / 2 : ℚ≥0)).kernel () none) (fun t => C (fanRead t)) =
      (if C (some true) then 1 else 0) + (if C (some false) then 1 else 0) :=
  (closedSum_fanKernel 2 (1 / 2 : ℚ≥0) (fun t => C (fanRead t))).trans (fan_pair_sum C)

theorem divided_some_zero (b : Bool) (target : (fanSpace 2).Term) :
    (fanSystem 2 (1 / 2 : ℚ≥0)).kernel () (some (b, (0 : Fin 2))) target = 0 := by
  show fanStep 2 (1 / 2 : ℚ≥0) (some (b, (0 : Fin 2))) target = 0
  rfl

/-- **(b) Weight-preserving.** Each outcome `1` is the sum of two copies of `1/2`. -/
theorem divided_preserving : KernelPreserving dividedFan := by
  intro label sourceTerm C _
  have labelUnit : label = () := Unit.eq_unit label
  subst labelUnit
  rcases quiet_cases sourceTerm with rfl | ⟨b, rfl⟩
  · have sourceSide :
        closedSum (dividedFan.source.kernel () none) C =
          (if C (some true) then 1 else 0) + (if C (some false) then 1 else 0) := by
      have fold : closedSum (dividedFan.source.kernel () none) C =
          closedSum ((outcomeSystem (1 : ℚ≥0)).kernel () none) C := rfl
      exact fold.trans (divided_source_sum C)
    have targetSide :
        closedSum (dividedFan.target.kernel (dividedFan.labelMap ()) (dividedFan.term none))
          (fun t => C (dividedFan.readBack t)) =
          (if C (some true) then 1 else 0) + (if C (some false) then 1 else 0) := by
      have fold :
          closedSum (dividedFan.target.kernel (dividedFan.labelMap ()) (dividedFan.term none))
            (fun t => C (dividedFan.readBack t)) =
            closedSum ((fanSystem 2 (1 / 2 : ℚ≥0)).kernel () none) (fun t => C (fanRead t)) := rfl
      exact fold.trans (divided_target_sum C)
    exact sourceSide.trans targetSide.symm
  · have sourceRow : dividedFan.source.kernel () (some b) = 0 := by
      show outcomeStep (1 : ℚ≥0) (some b) = 0
      rfl
    have targetRow :
        dividedFan.target.kernel () (quietEmbed 2 (by decide) (some b)) = 0 := by
      show fanStep 2 (1 / 2 : ℚ≥0) (quietEmbed 2 (by decide) (some b)) = 0
      rfl
    exact ((congrArg (fun row => closedSum row C) sourceRow).trans (closedSum_zero C)).trans
      ((congrArg (fun row => closedSum row (fun t => C (dividedFan.readBack t))) targetRow).trans
        (closedSum_zero _)).symm

theorem divided_term_resp {first second : quiet.Term} (equivalent : quiet.Equiv first second) :
    (fanSpace 2).Equiv (dividedFan.term first) (dividedFan.term second) := by
  cases equivalent
  rfl

noncomputable def dividedTerms : ContextMap (supportTheory (outcomeSystem (1 : ℚ≥0))
      (nonnegative_rat_noCancellation) ())
    (supportTheory (fanSystem 2 (1 / 2 : ℚ≥0)) nonnegative_rat_noCancellation ()) :=
  supportOfTerms dividedFan nonnegative_rat_noCancellation () divided_term_resp

theorem divided_image_hits_index_one :
    (supportGSLT (fanSystem 2 (1 / 2 : ℚ≥0)) nonnegative_rat_noCancellation ()).rewrites
      (dividedFan.term none) (some (true, (1 : Fin 2))) :=
  ⟨some (true, (1 : Fin 2)),
    Finsupp.mem_support_iff.mpr ((fanSystem_coeff 2 (1 / 2 : ℚ≥0) (true, 1)).symm ▸
      div_ne_zero one_ne_zero (by decide : (2 : ℚ≥0) ≠ 0)),
    rfl⟩

theorem divided_source_successors (next : quiet.Term)
    (step : (supportGSLT (outcomeSystem (1 : ℚ≥0)) nonnegative_rat_noCancellation ()).rewrites
      none next) :
    next = some true ∨ next = some false := by
  rcases (outcome_support_iff (1 : ℚ≥0) nonnegative_rat_noCancellation none next).mp step with
    ⟨_, _, b, rfl⟩
  cases b
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- **(b) Not Hosting.** `some (true, 1)` is a successor of the image of the
start, and it is not the image of any source successor. -/
theorem divided_not_hosting : ¬ dividedTerms.Hosting := by
  intro hosting
  have hosted :
      (ContextMap.ofTerms
        (source := supportGSLT (outcomeSystem (1 : ℚ≥0)) nonnegative_rat_noCancellation ())
        (target := supportTheory (fanSystem 2 (1 / 2 : ℚ≥0)) nonnegative_rat_noCancellation ())
        PUnit.unit dividedFan.term divided_term_resp).Hosting :=
    hosting
  rcases (ContextMap.ofTerms_hosting_iff
      (source := supportGSLT (outcomeSystem (1 : ℚ≥0)) nonnegative_rat_noCancellation ())
      (target := supportTheory (fanSystem 2 (1 / 2 : ℚ≥0)) nonnegative_rat_noCancellation ())
      PUnit.unit dividedFan.term divided_term_resp).mp hosted with ⟨_, _, reflects⟩
  have step := divided_image_hits_index_one
  obtain ⟨sourceNext, sourceStep, identified⟩ := reflects none (some (true, (1 : Fin 2))) step
  rcases divided_source_successors sourceNext sourceStep with rfl | rfl
  · exact quietEmbed_misses (some true) identified.symm
  · exact quietEmbed_misses (some false) identified.symm

/-- **Weight preservation does not give Exhausting.** The same missing successor
is a target term no source context names. -/
theorem divided_not_exhausting : ¬ dividedTerms.Exhausting := by
  intro exhausting
  obtain ⟨preimage, identified⟩ :=
    ContextMap.Exhausting.term_surjective (map := dividedTerms) exhausting
      (origin := PUnit.unit) (some (true, (1 : Fin 2)))
  exact quietEmbed_misses preimage identified.symm

/-- **The section fails on the divided fan.** The successor at index `1` reads
back to `some true`, and the embedding sends that to index `0`. -/
theorem divided_section_fails :
    ¬ (supportGSLT (fanSystem 2 (1 / 2 : ℚ≥0)) nonnegative_rat_noCancellation ()).Equiv
      (dividedFan.term (dividedFan.readBack (some (true, (1 : Fin 2)))))
      (some (true, (1 : Fin 2))) := by
  intro same
  exact quietEmbed_misses (some true) same

/-! ## Section: preservation and the two transition laws -/

theorem class_closed {S : GSLT} (point : S.Term) :
    ∀ x y, S.Equiv x y → (S.Equiv x point ↔ S.Equiv y point) :=
  ProbabilisticSystem.equiv_closed point

theorem preimage_closed {sourceSpace targetSpace : GSLT}
    (readBack : targetSpace.Term → sourceSpace.Term)
    (resp : ∀ {left right : targetSpace.Term}, targetSpace.Equiv left right →
      sourceSpace.Equiv (readBack left) (readBack right))
    (C : sourceSpace.Term → Prop)
    (closed : ∀ x y, sourceSpace.Equiv x y → (C x ↔ C y)) :
    ∀ x y, targetSpace.Equiv x y →
      ((fun t => C (readBack t)) x ↔ (fun t => C (readBack t)) y) :=
  fun _ _ equivalent => closed _ _ (resp equivalent)

/-- **(c) Forward.** Least hypotheses: closed-sum preservation, no cancellation,
`F` respects the equations, and `F` after the read-back is the identity up to
the equations on every support successor of an image. -/
theorem kernelPreserving_support_transitions {K : Type*} [Semiring K]
    {sourceSpace targetSpace : GSLT} (map : KernelMap K sourceSpace targetSpace)
    (noCancel : NoCancellation K) (preserves : KernelPreserving map)
    (label : map.source.Label)
    (term_resp : ∀ {first second : sourceSpace.Term}, sourceSpace.Equiv first second →
      targetSpace.Equiv (map.term first) (map.term second))
    (returns : ∀ {s : sourceSpace.Term} {y : targetSpace.Term},
      (supportGSLT map.target noCancel (map.labelMap label)).rewrites (map.term s) y →
        targetSpace.Equiv (map.term (map.readBack y)) y) :
    (supportOfTerms map noCancel label term_resp).PreservesTransitions ∧
      (supportOfTerms map noCancel label term_resp).ReflectsTransitions := by
  let induced := supportOfTerms map noCancel label term_resp
  have forwardRewrites : induced.PreservesRewrites := by
    intro _ s next step
    rcases step with ⟨x, member, close⟩
    have sourceNonzero :
        closedSum (map.source.kernel label s) (fun z => sourceSpace.Equiv z next) ≠ 0 :=
      (closedSum_ne_zero_iff noCancel _ _).mpr ⟨x, member, close⟩
    have sums := preserves label s (fun z => sourceSpace.Equiv z next) (class_closed next)
    have targetNonzero :
        closedSum (map.target.kernel (map.labelMap label) (map.term s))
          (fun t => sourceSpace.Equiv (map.readBack t) next) ≠ 0 := by
      rw [← sums]
      exact sourceNonzero
    obtain ⟨y, memberY, reads⟩ :=
      (closedSum_ne_zero_iff noCancel _ _).mp targetNonzero
    have targetStep :
        (supportGSLT map.target noCancel (map.labelMap label)).rewrites (map.term s) y :=
      ⟨y, memberY, targetSpace.equations.iseqv.refl y⟩
    have back : targetSpace.Equiv (map.term (map.readBack y)) y := returns targetStep
    have carried : targetSpace.Equiv (map.term (map.readBack y)) (map.term next) :=
      term_resp reads
    have toImage : targetSpace.Equiv y (map.term next) :=
      targetSpace.equations.iseqv.trans (targetSpace.equations.iseqv.symm back) carried
    exact (supportGSLT map.target noCancel (map.labelMap label)).rewrites_resp_right
      targetStep toImage
  have backwardRewrites : induced.ReflectsRewrites := by
    intro _ s y step
    have sectioned : targetSpace.Equiv (map.term (map.readBack y)) y := returns step
    rcases step with ⟨z, member, close⟩
    have readsZ : sourceSpace.Equiv (map.readBack z) (map.readBack y) :=
      map.readBack_resp close
    have targetNonzero :
        closedSum (map.target.kernel (map.labelMap label) (map.term s))
          (fun t => sourceSpace.Equiv (map.readBack t) (map.readBack y)) ≠ 0 :=
      (closedSum_ne_zero_iff noCancel _ _).mpr ⟨z, member, readsZ⟩
    have sums := preserves label s
      (fun point => sourceSpace.Equiv point (map.readBack y))
      (class_closed (map.readBack y))
    have sourceNonzero :
        closedSum (map.source.kernel label s)
          (fun point => sourceSpace.Equiv point (map.readBack y)) ≠ 0 := by
      rw [sums]
      exact targetNonzero
    obtain ⟨x, memberX, closeX⟩ := (closedSum_ne_zero_iff noCancel _ _).mp sourceNonzero
    exact ⟨map.readBack y, ⟨x, memberX, closeX⟩,
      targetSpace.equations.iseqv.symm sectioned⟩
  exact ⟨induced.preservesTransitions_of_rewrites forwardRewrites,
    induced.reflectsTransitions_of_rewrites backwardRewrites⟩

/-- **(c) Converse, over `OrBool`.** Least hypotheses: both transition laws,
and the read-back after `F` is the identity up to the equations on support
successors of the source. The forward section is not required. -/
theorem orBool_transitions_kernelPreserving
    {sourceSpace targetSpace : GSLT} (map : KernelMap OrBool sourceSpace targetSpace)
    (term_resp : ∀ {first second : sourceSpace.Term}, sourceSpace.Equiv first second →
      targetSpace.Equiv (map.term first) (map.term second))
    (preservesT : ∀ label,
      (supportOfTerms map OrBool.noCancellation label term_resp).PreservesTransitions)
    (reflectsT : ∀ label,
      (supportOfTerms map OrBool.noCancellation label term_resp).ReflectsTransitions)
    (retract : ∀ label {s : sourceSpace.Term} {next : sourceSpace.Term},
      (supportGSLT map.source OrBool.noCancellation label).rewrites s next →
        sourceSpace.Equiv (map.readBack (map.term next)) next) :
    KernelPreserving map := by
  intro label s C closed
  have forward :
      (supportOfTerms map OrBool.noCancellation label term_resp).PreservesRewrites := by
    exact ContextMap.preservesRewrites_of_transitions
      (map := supportOfTerms map OrBool.noCancellation label term_resp) (preservesT label)
  have backward :
      (supportOfTerms map OrBool.noCancellation label term_resp).ReflectsRewrites := by
    exact ContextMap.reflectsRewrites_of_transitions
      (map := supportOfTerms map OrBool.noCancellation label term_resp) (reflectsT label)
  have nonzeroIff :
      closedSum (map.source.kernel label s) C ≠ 0 ↔
        closedSum (map.target.kernel (map.labelMap label) (map.term s))
          (fun t => C (map.readBack t)) ≠ 0 := by
    constructor
    · intro nonzero
      obtain ⟨x, member, holds⟩ := (closedSum_ne_zero_iff OrBool.noCancellation _ _).mp nonzero
      have sourceStep : (supportGSLT map.source OrBool.noCancellation label).rewrites s x :=
        ⟨x, member, sourceSpace.equations.iseqv.refl x⟩
      have targetStep := forward (interface := PUnit.unit) sourceStep
      rcases targetStep with ⟨y, memberY, closeY⟩
      have reads : sourceSpace.Equiv (map.readBack y) x :=
        sourceSpace.equations.iseqv.trans (map.readBack_resp closeY)
          (retract label sourceStep)
      exact (closedSum_ne_zero_iff OrBool.noCancellation _ _).mpr
        ⟨y, memberY, (closed (map.readBack y) x reads).mpr holds⟩
    · intro nonzero
      obtain ⟨y, member, holds⟩ := (closedSum_ne_zero_iff OrBool.noCancellation _ _).mp nonzero
      have targetStep :
          (supportGSLT map.target OrBool.noCancellation (map.labelMap label)).rewrites
            (map.term s) y :=
        ⟨y, member, targetSpace.equations.iseqv.refl y⟩
      obtain ⟨sourceNext, sourceStep, identified⟩ :=
        backward (interface := PUnit.unit) targetStep
      have back : sourceSpace.Equiv (map.readBack y) sourceNext :=
        sourceSpace.equations.iseqv.trans (map.readBack_resp identified)
          (retract label sourceStep)
      rcases sourceStep with ⟨x, memberX, closeX⟩
      have inClass : C x := by
        have moved : sourceSpace.Equiv x (map.readBack y) :=
          sourceSpace.equations.iseqv.trans closeX (sourceSpace.equations.iseqv.symm back)
        exact (closed x (map.readBack y) moved).mpr holds
      exact (closedSum_ne_zero_iff OrBool.noCancellation _ _).mpr ⟨x, memberX, inClass⟩
  by_cases zeroS : closedSum (map.source.kernel label s) C = 0
  · have zeroT :
        closedSum (map.target.kernel (map.labelMap label) (map.term s))
          (fun t => C (map.readBack t)) = 0 := by
      by_contra nonzero
      exact nonzeroIff.mpr nonzero zeroS
    rw [zeroS, zeroT]
  · have nonzeroT := nonzeroIff.mp zeroS
    exact (orBool_eq_one_of_ne_zero zeroS).trans (orBool_eq_one_of_ne_zero nonzeroT).symm

end Mettapedia.Logic.HostingStyles.Weighted
