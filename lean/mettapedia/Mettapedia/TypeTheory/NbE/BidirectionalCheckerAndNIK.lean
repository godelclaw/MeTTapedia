import Mettapedia.TypeTheory.NbE.VerifiedRung
import Mettapedia.TypeTheory.NbE.NormalFormsAndConversion
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Checking
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.ExecutableChecking
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.ExecutableTowerChoices
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.ExecutableTowerNumbers
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerChecking
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.ExecutableCheckingControls

/-!
# NbE-backed bidirectional checking and finite evidence replay

The bidirectional algorithms use the closure-based weak-head reducer
`nbeWhnfReducer`. They are sound under the existing normalization interfaces.
For the cumulative universe tower with empty declaration-root computation and
rigid heads, they are complete at some finite fuel on the stated bidirectional
fragment. Raw term checking takes a formed expected type as a premise; full
judgment checking computes context and expected-type formation itself. The
computing natural-number instance has separate soundness and execution controls.

Structural typing trees and formation-sensitive derivation graphs can instead
carry a fuel bound for verified `nbeConvNf` conversion. Their replay is sound.
Certificate coverage additionally requires `UniverseRegularity` and
`TypedConvComplete` for formed type-conversion obligations; this module does not
establish that completeness hypothesis for arbitrary declaration roots. The
resulting indexed tree checker has `KernelAuthority.Checker.Authority` under
those same assumptions. Native codecs and execution refinement are separate.

Positive and separating negative controls cover eta, cumulative levels, dependent
identity endpoints and recursor computation. Beta-chain comparisons retain the
actual optional machine-step count, explicit path length and certificate-tree
size. These syntactic measurements are separate from native runtime costs.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.NbE

open Mettapedia.Logic
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.TypedEquality
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.TypedEquality.Normalization

/-! ## Bidirectional checking with closure-based NbE -/

section GenericNbEChecking

variable {Head : Type} (R : Rules Head) [DecidableEq Head] [DecidableRel R.headEq]
variable [∀ head, Decidable (R.isUniverse head)] [DecidableRel R.cumulative]
variable (choices : ExecutableChecking.HeadChoices R)
variable (root : ExecutableReduction.RootEvaluator R)

/-- Subtype checking (`BelowAlgorithm`) powered by `nbeWhnfReducer R root`. -/
def nbeBelow (fuel : Nat) {n : Nat} (Γ : Ctx Head n) (A B : Tm Head n) :
    Option (PLift (BelowAlgorithm R Γ A B)) :=
  ExecutableChecking.below R (nbeWhnfReducer R root) fuel Γ A B

/-- Bidirectional type synthesis powered by the closure-based weak-head NbE
reducer `nbeWhnfReducer R root`. -/
def nbeSynth (fuel : Nat) {n : Nat} (Γ : Ctx Head n) (t : Tm Head n) :
    Option (ExecutableChecking.SynthResult R Γ t) :=
  ExecutableChecking.synth R choices (nbeWhnfReducer R root) fuel Γ t

/-- Bidirectional type checking powered by `nbeWhnfReducer R root`. -/
def nbeCheck (fuel : Nat) {n : Nat} (Γ : Ctx Head n) (t A : Tm Head n) :
    Option (ExecutableChecking.CheckResult R Γ t A) :=
  ExecutableChecking.check R choices (nbeWhnfReducer R root) fuel Γ t A

/-- Context formation checking powered by `nbeWhnfReducer R root`. -/
def nbeFormContext (fuel : Nat) {n : Nat} (Γ : Ctx Head n) :
    Option (PLift (ExecutableChecking.ContextAlgorithm R Γ)) :=
  ExecutableChecking.formContext R choices (nbeWhnfReducer R root) fuel Γ

/-- Full judgment checking (context formation + expected-type formation +
bidirectional term checking) powered by `nbeWhnfReducer R root`. -/
def nbeJudgment (fuel : Nat) {n : Nat} (Γ : Ctx Head n) (t A : Tm Head n) :
    Option (ExecutableChecking.JudgmentCertificate R Γ t A) :=
  ExecutableChecking.judgment R choices (nbeWhnfReducer R root) fuel Γ t A

/-- Boolean judgment acceptance powered by `nbeWhnfReducer R root`. -/
def nbeAccepts (fuel : Nat) {n : Nat} (Γ : Ctx Head n) (t A : Tm Head n) : Bool :=
  ExecutableChecking.accepts R choices (nbeWhnfReducer R root) fuel Γ t A

/-- Qualified typed equality checking (checking both endpoints at `A` in `Γ`
and comparing them via type-directed NbE conversion) powered by `nbeWhnfReducer R root`. -/
def nbeAcceptsEquality (fuel : Nat) {n : Nat} (Γ : Ctx Head n)
    (t u A : Tm Head n) : Bool :=
  ExecutableChecking.acceptsEquality R choices (nbeWhnfReducer R root) fuel Γ t u A

/-! ### Fuel Monotonicity of Closure-Based NbE Checking -/

omit [DecidableEq Head] [DecidableRel R.headEq] [∀ head, Decidable (R.isUniverse head)] [DecidableRel R.cumulative] in
/-- Because `ExecutableReduction.Result R t` has a `Prop`-valued second field
(`Reduces R t target`), fuel monotonicity of `nbeWhnfReducer` preserves the exact
`Result` value. -/
theorem nbeWhnfReducer_mono_eq
    {fuel₁ fuel₂ n : Nat} {t : Tm Head n} {res : ExecutableReduction.Result R t}
    (hle : fuel₁ ≤ fuel₂)
    (h1 : nbeWhnfReducer R root fuel₁ t = some res) :
    nbeWhnfReducer R root fuel₂ t = some res := by
  exact (Subtype.ext rfl : (⟨res.val, _⟩ : ExecutableReduction.Result R t) = res) ▸
    nbeWhnfReducer_mono R root hle h1

omit [DecidableRel R.cumulative] in
/-- Fuel monotonicity of `ExecutableConversion.compare` with `nbeWhnfReducer`,
preserving the exact `PLift (Algorithm ...)` certificate by proof irrelevance. -/
theorem nbeCompare_mono_eq
    {fuel₁ fuel₂ n : Nat} {Γ : Ctx Head n} {t u A : Tm Head n}
    {res : PLift (Algorithm R (.compare Γ t u A))}
    (hle : fuel₁ ≤ fuel₂)
    (h1 : ExecutableConversion.compare R (nbeWhnfReducer R root) fuel₁ Γ t u A = some res) :
    ExecutableConversion.compare R (nbeWhnfReducer R root) fuel₂ Γ t u A = some res := by
  obtain ⟨res₂, h2⟩ := nbeCompare_mono R root hle h1
  have hEq : res₂ = res := Subsingleton.elim res₂ res
  exact hEq ▸ h2

omit [DecidableRel R.cumulative] in
/-- Fuel monotonicity of `ExecutableConversion.types` with `nbeWhnfReducer`,
preserving the exact `PLift (Algorithm ...)` certificate by proof irrelevance. -/
theorem nbeCompareTypes_mono_eq
    {fuel₁ fuel₂ n : Nat} {Γ : Ctx Head n} {A B : Tm Head n}
    {res : PLift (Algorithm R (.types Γ A B))}
    (hle : fuel₁ ≤ fuel₂)
    (h1 : ExecutableConversion.types R (nbeWhnfReducer R root) fuel₁ Γ A B = some res) :
    ExecutableConversion.types R (nbeWhnfReducer R root) fuel₂ Γ A B = some res := by
  obtain ⟨res₂, h2⟩ := nbeCompareTypes_mono R root hle h1
  have hEq : res₂ = res := Subsingleton.elim res₂ res
  exact hEq ▸ h2

omit [DecidableEq Head] [DecidableRel R.headEq] [DecidableRel R.cumulative] in
/-- Fuel monotonicity of `ExecutableChecking.asUniverse` with `nbeWhnfReducer`. -/
theorem asUniverse_mono_eq
    {fuel₁ fuel₂ n : Nat} {type : Tm Head n}
    {res : {head : Head // R.isUniverse head ∧ Reduces R type (.head head)}}
    (hle : fuel₁ ≤ fuel₂)
    (h1 : ExecutableChecking.asUniverse R (nbeWhnfReducer R root) fuel₁ type = some res) :
    ExecutableChecking.asUniverse R (nbeWhnfReducer R root) fuel₂ type = some res := by
  unfold ExecutableChecking.asUniverse at h1 ⊢
  cases hN : nbeWhnfReducer R root fuel₁ type with
  | none => simp [hN, bind, Option.bind] at h1
  | some normal =>
      rw [nbeWhnfReducer_mono_eq R root hle hN]
      simpa [hN] using h1

/-- Fuel monotonicity of `ExecutableChecking.below` (`nbeBelow`) with `nbeWhnfReducer`. -/
theorem nbeBelow_mono_eq
    {fuel₁ fuel₂ n : Nat} {Γ : Ctx Head n} {A B : Tm Head n}
    {res : PLift (BelowAlgorithm R Γ A B)}
    (hle : fuel₁ ≤ fuel₂)
    (h1 : ExecutableChecking.below R (nbeWhnfReducer R root) fuel₁ Γ A B = some res) :
    ExecutableChecking.below R (nbeWhnfReducer R root) fuel₂ Γ A B = some res := by
  induction fuel₁ generalizing fuel₂ n Γ A B with
  | zero => cases h1
  | succ f₁ ih =>
      cases fuel₂ with
      | zero => omega
      | succ f₂ =>
          have hf : f₁ ≤ f₂ := by omega
          have hf1 : f₁ + 1 ≤ f₂ + 1 := by omega
          unfold ExecutableChecking.below at h1 ⊢
          cases hT2 : ExecutableConversion.types R (nbeWhnfReducer R root) (f₂ + 1) Γ A B with
          | some same₂ =>
              exact congrArg some (Subsingleton.elim _ _)
          | none =>
              cases hT1 : ExecutableConversion.types R (nbeWhnfReducer R root) (f₁ + 1) Γ A B with
              | some same₁ =>
                  have hT2' := nbeCompareTypes_mono_eq R root hf1 hT1
                  rw [hT2] at hT2'
                  cases hT2'
              | none =>
                  simp only [hT1] at h1
                  cases hNA : nbeWhnfReducer R root (f₁ + 1) A with
                  | none => simp [hNA, bind, Option.bind] at h1
                  | some nA =>
                      cases hNB : nbeWhnfReducer R root (f₁ + 1) B with
                      | none => simp [hNA, hNB, bind, Option.bind] at h1
                      | some nB =>
                          rw [nbeWhnfReducer_mono_eq R root hf1 hNA,
                              nbeWhnfReducer_mono_eq R root hf1 hNB]
                          simp only [hNA, hNB, bind, Option.bind] at h1 ⊢
                          rcases nA with ⟨vA, pA⟩
                          rcases nB with ⟨vB, pB⟩
                          cases vA <;> cases vB <;> try exact h1
                          · rename_i domA codA domB codB
                            simp only at h1 ⊢
                            cases hDom : ExecutableConversion.types R (nbeWhnfReducer R root) f₁ Γ domA domB with
                            | none => simp [hDom] at h1
                            | some dDom =>
                                cases hCod : ExecutableChecking.below R (nbeWhnfReducer R root) f₁ (.snoc Γ domA) codA codB with
                                | none => simp [hDom, hCod] at h1
                                | some dCod =>
                                    rw [nbeCompareTypes_mono_eq R root hf hDom, ih hf hCod]
                                    simp [hDom, hCod] at h1 ⊢
                          · rename_i domA codA domB codB
                            simp only at h1 ⊢
                            cases hDom : ExecutableChecking.below R (nbeWhnfReducer R root) f₁ Γ domA domB with
                            | none => simp [hDom] at h1
                            | some dDom =>
                                cases hCod : ExecutableChecking.below R (nbeWhnfReducer R root) f₁ (.snoc Γ domA) codA codB with
                                | none => simp [hDom, hCod] at h1
                                | some dCod =>
                                    rw [ih hf hDom, ih hf hCod]
                                    simp [hDom, hCod] at h1 ⊢

private theorem option_bind_mono_eq {α β : Type} {ma₁ ma₂ : Option α}
    {f₁ f₂ : α → Option β} {b : β}
    (h1 : ma₁.bind f₁ = some b)
    (hma : ∀ a, ma₁ = some a → ma₂ = some a)
    (hf : ∀ a, ma₁ = some a → f₁ a = some b → f₂ a = some b) :
    ma₂.bind f₂ = some b := by
  cases ha : ma₁ with
  | none => simp [ha] at h1
  | some a =>
      rw [hma a ha]
      exact hf a ha (by simpa [ha] using h1)

/-- Simultaneous fuel monotonicity of `ExecutableChecking.synth` and
`ExecutableChecking.check` with `nbeWhnfReducer`. -/
theorem nbeSynthCheck_mono_eq :
    ∀ (fuel₁ : Nat),
      (∀ {fuel₂ n : Nat} {Γ : Ctx Head n} {t : Tm Head n}
        {res : ExecutableChecking.SynthResult R Γ t},
        fuel₁ ≤ fuel₂ →
        ExecutableChecking.synth R choices (nbeWhnfReducer R root) fuel₁ Γ t = some res →
        ExecutableChecking.synth R choices (nbeWhnfReducer R root) fuel₂ Γ t = some res) ∧
      (∀ {fuel₂ n : Nat} {Γ : Ctx Head n} {t A : Tm Head n}
        {res : ExecutableChecking.CheckResult R Γ t A},
        fuel₁ ≤ fuel₂ →
        ExecutableChecking.check R choices (nbeWhnfReducer R root) fuel₁ Γ t A = some res →
        ExecutableChecking.check R choices (nbeWhnfReducer R root) fuel₂ Γ t A = some res)
  | 0 =>
      ⟨fun _ h1 => (by cases h1), fun _ h1 => (by cases h1)⟩
  | f₁ + 1 =>
      let ⟨ihSynth, ihCheck⟩ := nbeSynthCheck_mono_eq f₁
      ⟨by
        intro fuel₂ n Γ t res hle h1
        cases fuel₂ with
        | zero => omega
        | succ f₂ =>
            have hf : f₁ ≤ f₂ := by omega
            have hf1 : f₁ + 1 ≤ f₂ + 1 := by omega
            unfold ExecutableChecking.synth at h1 ⊢
            cases t with
            | var i => exact h1
            | const name => exact h1
            | head value => exact h1
            | lam _ => exact h1
            | pair _ _ => exact h1
            | refl subject =>
                simp only [bind] at h1 ⊢
                exact option_bind_mono_eq h1 (fun _ ha => ihSynth hf ha) (fun _ _ h => h)
            | pi domain body =>
                simp only [bind] at h1 ⊢
                refine option_bind_mono_eq h1 (fun _ ha => ihSynth hf ha) (fun _ _ h1 => ?_)
                refine option_bind_mono_eq h1 (fun _ ha => asUniverse_mono_eq R root hf1 ha) (fun _ _ h1 => ?_)
                refine option_bind_mono_eq h1 (fun _ ha => ihSynth hf ha) (fun _ _ h1 => ?_)
                refine option_bind_mono_eq h1 (fun _ ha => asUniverse_mono_eq R root hf1 ha) (fun _ _ h1 => h1)
            | sigma domain body =>
                simp only [bind] at h1 ⊢
                refine option_bind_mono_eq h1 (fun _ ha => ihSynth hf ha) (fun _ _ h1 => ?_)
                refine option_bind_mono_eq h1 (fun _ ha => asUniverse_mono_eq R root hf1 ha) (fun _ _ h1 => ?_)
                refine option_bind_mono_eq h1 (fun _ ha => ihSynth hf ha) (fun _ _ h1 => ?_)
                refine option_bind_mono_eq h1 (fun _ ha => asUniverse_mono_eq R root hf1 ha) (fun _ _ h1 => h1)
            | id carrier left right =>
                simp only [bind] at h1 ⊢
                refine option_bind_mono_eq h1 (fun _ ha => ihSynth hf ha) (fun _ _ h1 => ?_)
                refine option_bind_mono_eq h1 (fun _ ha => asUniverse_mono_eq R root hf1 ha) (fun _ _ h1 => ?_)
                refine option_bind_mono_eq h1 (fun _ ha => ihCheck hf ha) (fun _ _ h1 => ?_)
                refine option_bind_mono_eq h1 (fun _ ha => ihCheck hf ha) (fun _ _ h1 => h1)
            | fst pair =>
                simp only [bind] at h1 ⊢
                refine option_bind_mono_eq h1 (fun _ ha => ihSynth hf ha) (fun _ _ h1 => ?_)
                exact option_bind_mono_eq h1 (fun _ ha => nbeWhnfReducer_mono_eq R root hf1 ha) (fun _ _ h1 => h1)
            | snd pair =>
                simp only [bind] at h1 ⊢
                refine option_bind_mono_eq h1 (fun _ ha => ihSynth hf ha) (fun _ _ h1 => ?_)
                exact option_bind_mono_eq h1 (fun _ ha => nbeWhnfReducer_mono_eq R root hf1 ha) (fun _ _ h1 => h1)
            | app fn arg =>
                cases fn with
                | lam body =>
                    simp only [bind] at h1 ⊢
                    refine option_bind_mono_eq h1 (fun _ ha => ihSynth hf ha) (fun _ _ h1 => ?_)
                    exact option_bind_mono_eq h1 (fun _ ha => ihSynth hf ha) (fun _ _ h1 => h1)
                | var _ | const _ | head _ | pi _ _ | sigma _ _ | id _ _ _ | app _ _ | pair _ _ | fst _ | snd _ | refl _ =>
                    simp only [bind] at h1 ⊢
                    refine option_bind_mono_eq h1 (fun _ ha => ihSynth hf ha) (fun _ _ h1 => ?_)
                    refine option_bind_mono_eq h1 (fun _ ha => nbeWhnfReducer_mono_eq R root hf1 ha) (fun normal _ h1 => ?_)
                    rcases normal with ⟨v, pv⟩
                    cases v <;> try exact h1
                    simp only at h1 ⊢
                    exact option_bind_mono_eq h1 (fun _ ha => ihCheck hf ha) (fun _ _ h1 => h1),
      by
        intro fuel₂ n Γ t A res hle h1
        cases fuel₂ with
        | zero => omega
        | succ f₂ =>
            have hf : f₁ ≤ f₂ := by omega
            have hf1 : f₁ + 1 ≤ f₂ + 1 := by omega
            unfold ExecutableChecking.check at h1 ⊢
            cases t with
            | lam body =>
                simp only [bind] at h1 ⊢
                refine option_bind_mono_eq h1 (fun _ ha => nbeWhnfReducer_mono_eq R root hf1 ha) (fun normal _ h1 => ?_)
                rcases normal with ⟨v, pv⟩
                cases v <;> try exact h1
                simp only at h1 ⊢
                exact option_bind_mono_eq h1 (fun _ ha => ihCheck hf ha) (fun _ _ h1 => h1)
            | pair first second =>
                simp only [bind] at h1 ⊢
                refine option_bind_mono_eq h1 (fun _ ha => nbeWhnfReducer_mono_eq R root hf1 ha) (fun normal _ h1 => ?_)
                rcases normal with ⟨v, pv⟩
                cases v <;> try exact h1
                simp only at h1 ⊢
                refine option_bind_mono_eq h1 (fun _ ha => ihCheck hf ha) (fun _ _ h1 => ?_)
                exact option_bind_mono_eq h1 (fun _ ha => ihCheck hf ha) (fun _ _ h1 => h1)
            | refl subject =>
                simp only [bind] at h1 ⊢
                refine option_bind_mono_eq h1 (fun _ ha => nbeWhnfReducer_mono_eq R root hf1 ha) (fun normal _ h1 => ?_)
                rcases normal with ⟨v, pv⟩
                cases v <;> try exact h1
                simp only at h1 ⊢
                refine option_bind_mono_eq h1 (fun _ ha => ihCheck hf ha) (fun _ _ h1 => ?_)
                refine option_bind_mono_eq h1 (fun _ ha => nbeCompare_mono_eq R root hf ha) (fun _ _ h1 => ?_)
                exact option_bind_mono_eq h1 (fun _ ha => nbeCompare_mono_eq R root hf ha) (fun _ _ h1 => h1)
            | var _ | const _ | head _ | pi _ _ | sigma _ _ | id _ _ _ | app _ _ | fst _ | snd _ =>
                simp only [bind] at h1 ⊢
                refine option_bind_mono_eq h1 (fun _ ha => ihSynth hf ha) (fun _ _ h1 => ?_)
                exact option_bind_mono_eq h1 (fun _ ha => nbeBelow_mono_eq R root hf ha) (fun _ _ h1 => h1)⟩

theorem nbeSynth_mono_eq
    {fuel₁ fuel₂ n : Nat} {Γ : Ctx Head n} {t : Tm Head n}
    {res : ExecutableChecking.SynthResult R Γ t}
    (hle : fuel₁ ≤ fuel₂)
    (h1 : nbeSynth R choices root fuel₁ Γ t = some res) :
    nbeSynth R choices root fuel₂ Γ t = some res :=
  (nbeSynthCheck_mono_eq R choices root fuel₁).1 hle h1

theorem nbeCheck_mono_eq
    {fuel₁ fuel₂ n : Nat} {Γ : Ctx Head n} {t A : Tm Head n}
    {res : ExecutableChecking.CheckResult R Γ t A}
    (hle : fuel₁ ≤ fuel₂)
    (h1 : nbeCheck R choices root fuel₁ Γ t A = some res) :
    nbeCheck R choices root fuel₂ Γ t A = some res :=
  (nbeSynthCheck_mono_eq R choices root fuel₁).2 hle h1

theorem nbeFormContext_mono_eq
    {fuel₁ fuel₂ n : Nat} {Γ : Ctx Head n}
    {res : PLift (ExecutableChecking.ContextAlgorithm R Γ)}
    (hle : fuel₁ ≤ fuel₂)
    (h1 : nbeFormContext R choices root fuel₁ Γ = some res) :
    nbeFormContext R choices root fuel₂ Γ = some res := by
  induction Γ with
  | nil => exact h1
  | snoc ctx dom ih =>
      unfold nbeFormContext ExecutableChecking.formContext at h1 ⊢
      simp only [bind] at h1 ⊢
      refine option_bind_mono_eq h1 (fun _ ha => ih ha) (fun _ _ h1 => ?_)
      refine option_bind_mono_eq h1 (fun _ ha => nbeSynth_mono_eq R choices root hle ha) (fun _ _ h1 => ?_)
      exact option_bind_mono_eq h1 (fun _ ha => asUniverse_mono_eq R root hle ha) (fun _ _ h1 => h1)

/-! ### Per-Branch Construction Helpers for `ExecutableChecking` -/

omit [DecidableEq Head] [DecidableRel R.headEq] [DecidableRel R.cumulative] in
private theorem asUniverse_of_whnf
    {fuel n : Nat} {T : Tm Head n} {norm : ExecutableReduction.Result R T} {u : Head}
    (hNorm : nbeWhnfReducer R root fuel T = some norm)
    (hVal : norm.val = .head u)
    (hu : R.isUniverse u) :
    ∃ res, ExecutableChecking.asUniverse R (nbeWhnfReducer R root) fuel T = some res ∧
      res.val = u := by
  rcases norm with ⟨v, pv⟩
  dsimp at hVal
  subst hVal
  exact ⟨⟨u, hu, pv⟩, by simp [ExecutableChecking.asUniverse, hNorm, hu, bind, Option.bind], rfl⟩

private theorem below_of_types
    {fuel n : Nat} {Γ : Ctx Head n} {A B : Tm Head n}
    {same : PLift (Algorithm R (.types Γ A B))}
    (hTypes : ExecutableConversion.types R (nbeWhnfReducer R root) (fuel + 1) Γ A B = some same) :
    ∃ res, ExecutableChecking.below R (nbeWhnfReducer R root) (fuel + 1) Γ A B = some res := by
  refine ⟨⟨.conv same.down⟩, ?_⟩
  simp [ExecutableChecking.below, hTypes]

private theorem below_of_universes
    {fuel n : Nat} {Γ : Ctx Head n} {A B : Tm Head n}
    {nA : ExecutableReduction.Result R A} {nB : ExecutableReduction.Result R B} {u v : Head}
    (hNA : nbeWhnfReducer R root (fuel + 1) A = some nA) (hValA : nA.val = .head u)
    (hNB : nbeWhnfReducer R root (fuel + 1) B = some nB) (hValB : nB.val = .head v)
    (hCumul : R.cumulative u v) :
    ∃ res, ExecutableChecking.below R (nbeWhnfReducer R root) (fuel + 1) Γ A B = some res := by
  unfold ExecutableChecking.below
  cases hT : ExecutableConversion.types R (nbeWhnfReducer R root) (fuel + 1) Γ A B with
  | some same => exact ⟨⟨.conv same.down⟩, rfl⟩
  | none =>
      rcases nA with ⟨vA, pA⟩
      rcases nB with ⟨vB, pB⟩
      dsimp at hValA hValB
      subst hValA; subst hValB
      exact ⟨⟨.universes pA pB hCumul⟩, by simp [hNA, hNB, hCumul, bind, Option.bind, pure]⟩

private theorem below_of_pi
    {fuel n : Nat} {Γ : Ctx Head n} {A B A₁ A₂ : Tm Head n} {B₁ B₂ : Tm Head (n + 1)}
    {nA : ExecutableReduction.Result R A} {nB : ExecutableReduction.Result R B}
    {dDom : PLift (Algorithm R (.types Γ A₁ A₂))}
    {dCod : PLift (BelowAlgorithm R (.snoc Γ A₁) B₁ B₂)}
    (hNA : nbeWhnfReducer R root (fuel + 1) A = some nA) (hValA : nA.val = .pi A₁ B₁)
    (hNB : nbeWhnfReducer R root (fuel + 1) B = some nB) (hValB : nB.val = .pi A₂ B₂)
    (hDom : ExecutableConversion.types R (nbeWhnfReducer R root) fuel Γ A₁ A₂ = some dDom)
    (hCod : ExecutableChecking.below R (nbeWhnfReducer R root) fuel (.snoc Γ A₁) B₁ B₂ = some dCod) :
    ∃ res, ExecutableChecking.below R (nbeWhnfReducer R root) (fuel + 1) Γ A B = some res := by
  unfold ExecutableChecking.below
  cases hT : ExecutableConversion.types R (nbeWhnfReducer R root) (fuel + 1) Γ A B with
  | some same => exact ⟨⟨.conv same.down⟩, rfl⟩
  | none =>
      rcases nA with ⟨vA, pA⟩
      rcases nB with ⟨vB, pB⟩
      dsimp at hValA hValB
      subst hValA; subst hValB
      exact ⟨⟨.pi pA pB dDom.down dCod.down⟩,
        by simp [hNA, hNB, hDom, hCod, bind, Option.bind, pure]⟩

private theorem below_of_sigma
    {fuel n : Nat} {Γ : Ctx Head n} {A B A₁ A₂ : Tm Head n} {B₁ B₂ : Tm Head (n + 1)}
    {nA : ExecutableReduction.Result R A} {nB : ExecutableReduction.Result R B}
    {dDom : PLift (BelowAlgorithm R Γ A₁ A₂)}
    {dCod : PLift (BelowAlgorithm R (.snoc Γ A₁) B₁ B₂)}
    (hNA : nbeWhnfReducer R root (fuel + 1) A = some nA) (hValA : nA.val = .sigma A₁ B₁)
    (hNB : nbeWhnfReducer R root (fuel + 1) B = some nB) (hValB : nB.val = .sigma A₂ B₂)
    (hDom : ExecutableChecking.below R (nbeWhnfReducer R root) fuel Γ A₁ A₂ = some dDom)
    (hCod : ExecutableChecking.below R (nbeWhnfReducer R root) fuel (.snoc Γ A₁) B₁ B₂ = some dCod) :
    ∃ res, ExecutableChecking.below R (nbeWhnfReducer R root) (fuel + 1) Γ A B = some res := by
  unfold ExecutableChecking.below
  cases hT : ExecutableConversion.types R (nbeWhnfReducer R root) (fuel + 1) Γ A B with
  | some same => exact ⟨⟨.conv same.down⟩, rfl⟩
  | none =>
      rcases nA with ⟨vA, pA⟩
      rcases nB with ⟨vB, pB⟩
      dsimp at hValA hValB
      subst hValA; subst hValB
      exact ⟨⟨.sigma pA pB dDom.down dCod.down⟩,
        by simp [hNA, hNB, hDom, hCod, bind, Option.bind, pure]⟩

private theorem synth_pi_of
    {fuel n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {B : Tm Head (n + 1)}
    {rA : ExecutableChecking.SynthResult R Γ A}
    {uA : {head : Head // R.isUniverse head ∧ Reduces R rA.1 (.head head)}}
    {rB : ExecutableChecking.SynthResult R (.snoc Γ A) B}
    {uB : {head : Head // R.isUniverse head ∧ Reduces R rB.1 (.head head)}}
    {j : {result : Head // R.join uA.val uB.val result}}
    (hSA : ExecutableChecking.synth R choices (nbeWhnfReducer R root) fuel Γ A = some rA)
    (hUA : ExecutableChecking.asUniverse R (nbeWhnfReducer R root) (fuel + 1) rA.1 = some uA)
    (hSB : ExecutableChecking.synth R choices (nbeWhnfReducer R root) fuel (.snoc Γ A) B = some rB)
    (hUB : ExecutableChecking.asUniverse R (nbeWhnfReducer R root) (fuel + 1) rB.1 = some uB)
    (hJ : choices.join uA.val uB.val = some j) :
    ∃ res, ExecutableChecking.synth R choices (nbeWhnfReducer R root) (fuel + 1) Γ (.pi A B) = some res ∧
      res.1 = .head j.val := by
  refine ⟨⟨.head j.val, ⟨.pi rA.2.down uA.property.2 uA.property.1 rB.2.down uB.property.2 uB.property.1 j.property⟩⟩, ?_, rfl⟩
  simp [ExecutableChecking.synth, hSA, hUA, hSB, hUB, hJ, bind, Option.bind, pure]

private theorem synth_sigma_of
    {fuel n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {B : Tm Head (n + 1)}
    {rA : ExecutableChecking.SynthResult R Γ A}
    {uA : {head : Head // R.isUniverse head ∧ Reduces R rA.1 (.head head)}}
    {rB : ExecutableChecking.SynthResult R (.snoc Γ A) B}
    {uB : {head : Head // R.isUniverse head ∧ Reduces R rB.1 (.head head)}}
    {j : {result : Head // R.join uA.val uB.val result}}
    (hSA : ExecutableChecking.synth R choices (nbeWhnfReducer R root) fuel Γ A = some rA)
    (hUA : ExecutableChecking.asUniverse R (nbeWhnfReducer R root) (fuel + 1) rA.1 = some uA)
    (hSB : ExecutableChecking.synth R choices (nbeWhnfReducer R root) fuel (.snoc Γ A) B = some rB)
    (hUB : ExecutableChecking.asUniverse R (nbeWhnfReducer R root) (fuel + 1) rB.1 = some uB)
    (hJ : choices.join uA.val uB.val = some j) :
    ∃ res, ExecutableChecking.synth R choices (nbeWhnfReducer R root) (fuel + 1) Γ (.sigma A B) = some res ∧
      res.1 = .head j.val := by
  refine ⟨⟨.head j.val, ⟨.sigma rA.2.down uA.property.2 uA.property.1 rB.2.down uB.property.2 uB.property.1 j.property⟩⟩, ?_, rfl⟩
  simp [ExecutableChecking.synth, hSA, hUA, hSB, hUB, hJ, bind, Option.bind, pure]

private theorem synth_id_of
    {fuel n : Nat} {Γ : Ctx Head n} {A a b : Tm Head n}
    {rA : ExecutableChecking.SynthResult R Γ A}
    {uA : {head : Head // R.isUniverse head ∧ Reduces R rA.1 (.head head)}}
    {ca : ExecutableChecking.CheckResult R Γ a A}
    {cb : ExecutableChecking.CheckResult R Γ b A}
    (hSA : ExecutableChecking.synth R choices (nbeWhnfReducer R root) fuel Γ A = some rA)
    (hUA : ExecutableChecking.asUniverse R (nbeWhnfReducer R root) (fuel + 1) rA.1 = some uA)
    (hCA : ExecutableChecking.check R choices (nbeWhnfReducer R root) fuel Γ a A = some ca)
    (hCB : ExecutableChecking.check R choices (nbeWhnfReducer R root) fuel Γ b A = some cb) :
    ∃ res, ExecutableChecking.synth R choices (nbeWhnfReducer R root) (fuel + 1) Γ (.id A a b) = some res ∧
      res.1 = .head uA.val := by
  refine ⟨⟨.head uA.val, ⟨.id rA.2.down uA.property.2 uA.property.1 ca.down cb.down⟩⟩, ?_, rfl⟩
  simp [ExecutableChecking.synth, hSA, hUA, hCA, hCB, bind, Option.bind, pure]

private theorem synth_redex_of
    {fuel n : Nat} {Γ : Ctx Head n} {a : Tm Head n} {b : Tm Head (n + 1)}
    {rA : ExecutableChecking.SynthResult R Γ a}
    {rB : ExecutableChecking.SynthResult R (.snoc Γ rA.1) b}
    (hSA : ExecutableChecking.synth R choices (nbeWhnfReducer R root) fuel Γ a = some rA)
    (hSB : ExecutableChecking.synth R choices (nbeWhnfReducer R root) fuel (.snoc Γ rA.1) b = some rB) :
    ∃ res, ExecutableChecking.synth R choices (nbeWhnfReducer R root) (fuel + 1) Γ (.app (.lam b) a) = some res ∧
      res.1 = inst0 a rB.1 := by
  refine ⟨⟨inst0 a rB.1, ⟨.redex rA.2.down rB.2.down⟩⟩, ?_, rfl⟩
  simp [ExecutableChecking.synth, hSA, hSB, bind, Option.bind, pure]

private theorem synth_app_of
    {fuel n : Nat} {Γ : Ctx Head n} {f a A : Tm Head n} {B : Tm Head (n + 1)}
    {rF : ExecutableChecking.SynthResult R Γ f}
    {nF : ExecutableReduction.Result R rF.1}
    {ca : ExecutableChecking.CheckResult R Γ a A}
    (hNotLam : ∀ body, f ≠ .lam body)
    (hSF : ExecutableChecking.synth R choices (nbeWhnfReducer R root) fuel Γ f = some rF)
    (hNF : nbeWhnfReducer R root (fuel + 1) rF.1 = some nF) (hValF : nF.val = .pi A B)
    (hCA : ExecutableChecking.check R choices (nbeWhnfReducer R root) fuel Γ a A = some ca) :
    ∃ res, ExecutableChecking.synth R choices (nbeWhnfReducer R root) (fuel + 1) Γ (.app f a) = some res ∧
      res.1 = inst0 a B := by
  rcases nF with ⟨vF, pF⟩
  dsimp at hValF
  subst hValF
  refine ⟨⟨inst0 a B, ⟨.app rF.2.down pF ca.down⟩⟩, ?_, rfl⟩
  cases f with
  | lam body => exact False.elim (hNotLam body rfl)
  | var _ | const _ | head _ | pi _ _ | sigma _ _ | id _ _ _ | app _ _ | pair _ _ | fst _ | snd _ | refl _ =>
      simp [ExecutableChecking.synth, hSF, hNF, hCA, bind, Option.bind, pure]

private theorem synth_fst_of
    {fuel n : Nat} {Γ : Ctx Head n} {p A : Tm Head n} {B : Tm Head (n + 1)}
    {rP : ExecutableChecking.SynthResult R Γ p}
    {nP : ExecutableReduction.Result R rP.1}
    (hSP : ExecutableChecking.synth R choices (nbeWhnfReducer R root) fuel Γ p = some rP)
    (hNP : nbeWhnfReducer R root (fuel + 1) rP.1 = some nP) (hValP : nP.val = .sigma A B) :
    ∃ res, ExecutableChecking.synth R choices (nbeWhnfReducer R root) (fuel + 1) Γ (.fst p) = some res ∧
      res.1 = A := by
  rcases nP with ⟨vP, pP⟩
  dsimp at hValP
  subst hValP
  refine ⟨⟨A, ⟨.fst rP.2.down pP⟩⟩, ?_, rfl⟩
  simp [ExecutableChecking.synth, hSP, hNP, bind, Option.bind, pure]

private theorem synth_snd_of
    {fuel n : Nat} {Γ : Ctx Head n} {p A : Tm Head n} {B : Tm Head (n + 1)}
    {rP : ExecutableChecking.SynthResult R Γ p}
    {nP : ExecutableReduction.Result R rP.1}
    (hSP : ExecutableChecking.synth R choices (nbeWhnfReducer R root) fuel Γ p = some rP)
    (hNP : nbeWhnfReducer R root (fuel + 1) rP.1 = some nP) (hValP : nP.val = .sigma A B) :
    ∃ res, ExecutableChecking.synth R choices (nbeWhnfReducer R root) (fuel + 1) Γ (.snd p) = some res ∧
      res.1 = inst0 (.fst p) B := by
  rcases nP with ⟨vP, pP⟩
  dsimp at hValP
  subst hValP
  refine ⟨⟨inst0 (.fst p) B, ⟨.snd rP.2.down pP⟩⟩, ?_, rfl⟩
  simp [ExecutableChecking.synth, hSP, hNP, bind, Option.bind, pure]

private theorem check_lam_of
    {fuel n : Nat} {Γ : Ctx Head n} {body : Tm Head (n + 1)} {E A : Tm Head n} {B : Tm Head (n + 1)}
    {nE : ExecutableReduction.Result R E}
    {cb : ExecutableChecking.CheckResult R (.snoc Γ A) body B}
    (hNE : nbeWhnfReducer R root (fuel + 1) E = some nE) (hValE : nE.val = .pi A B)
    (hCB : ExecutableChecking.check R choices (nbeWhnfReducer R root) fuel (.snoc Γ A) body B = some cb) :
    ∃ res, ExecutableChecking.check R choices (nbeWhnfReducer R root) (fuel + 1) Γ (.lam body) E = some res := by
  rcases nE with ⟨vE, pE⟩
  dsimp at hValE
  subst hValE
  refine ⟨⟨.lamCheck pE cb.down⟩, ?_⟩
  simp [ExecutableChecking.check, hNE, hCB, bind, Option.bind, pure]

private theorem check_pair_of
    {fuel n : Nat} {Γ : Ctx Head n} {a b E A : Tm Head n} {B : Tm Head (n + 1)}
    {nE : ExecutableReduction.Result R E}
    {ca : ExecutableChecking.CheckResult R Γ a A}
    {cb : ExecutableChecking.CheckResult R Γ b (inst0 a B)}
    (hNE : nbeWhnfReducer R root (fuel + 1) E = some nE) (hValE : nE.val = .sigma A B)
    (hCA : ExecutableChecking.check R choices (nbeWhnfReducer R root) fuel Γ a A = some ca)
    (hCB : ExecutableChecking.check R choices (nbeWhnfReducer R root) fuel Γ b (inst0 a B) = some cb) :
    ∃ res, ExecutableChecking.check R choices (nbeWhnfReducer R root) (fuel + 1) Γ (.pair a b) E = some res := by
  rcases nE with ⟨vE, pE⟩
  dsimp at hValE
  subst hValE
  refine ⟨⟨.pairCheck pE ca.down cb.down⟩, ?_⟩
  simp [ExecutableChecking.check, hNE, hCA, hCB, bind, Option.bind, pure]

private theorem check_refl_of
    {fuel n : Nat} {Γ : Ctx Head n} {x E C a b : Tm Head n}
    {nE : ExecutableReduction.Result R E}
    {cx : ExecutableChecking.CheckResult R Γ x C}
    {cxa : PLift (Algorithm R (.compare Γ x a C))}
    {cxb : PLift (Algorithm R (.compare Γ x b C))}
    (hNE : nbeWhnfReducer R root (fuel + 1) E = some nE) (hValE : nE.val = .id C a b)
    (hCX : ExecutableChecking.check R choices (nbeWhnfReducer R root) fuel Γ x C = some cx)
    (hCXA : ExecutableConversion.compare R (nbeWhnfReducer R root) fuel Γ x a C = some cxa)
    (hCXB : ExecutableConversion.compare R (nbeWhnfReducer R root) fuel Γ x b C = some cxb) :
    ∃ res, ExecutableChecking.check R choices (nbeWhnfReducer R root) (fuel + 1) Γ (.refl x) E = some res := by
  rcases nE with ⟨vE, pE⟩
  dsimp at hValE
  subst hValE
  refine ⟨⟨.reflCheck pE cx.down cxa.down cxb.down⟩, ?_⟩
  simp [ExecutableChecking.check, hNE, hCX, hCXA, hCXB, bind, Option.bind, pure]

private theorem check_switch_of
    {fuel n : Nat} {Γ : Ctx Head n} {t E : Tm Head n}
    {rT : ExecutableChecking.SynthResult R Γ t}
    {u : PLift (BelowAlgorithm R Γ rT.1 E)}
    (hNotLam : ∀ body, t ≠ .lam body)
    (hNotPair : ∀ a b, t ≠ .pair a b)
    (hNotRefl : ∀ x, t ≠ .refl x)
    (hST : ExecutableChecking.synth R choices (nbeWhnfReducer R root) fuel Γ t = some rT)
    (hB : ExecutableChecking.below R (nbeWhnfReducer R root) fuel Γ rT.1 E = some u) :
    ∃ res, ExecutableChecking.check R choices (nbeWhnfReducer R root) (fuel + 1) Γ t E = some res := by
  refine ⟨⟨.switch rT.2.down u.down⟩, ?_⟩
  cases t with
  | lam body => exact False.elim (hNotLam body rfl)
  | pair a b => exact False.elim (hNotPair a b rfl)
  | refl x => exact False.elim (hNotRefl x rfl)
  | var _ | const _ | head _ | pi _ _ | sigma _ _ | id _ _ _ | app _ _ | fst _ | snd _ =>
      simp [ExecutableChecking.check, hST, hB, bind, Option.bind, pure]

end GenericNbEChecking

theorem Bidirectional.synth_not_lam {Head : Type} {n : Nat} {t : Tm Head n}
    (h : Bidirectional .synth t) : ∀ body, t ≠ .lam body := by
  intro body hEq; subst hEq; cases h

theorem Bidirectional.synth_not_pair {Head : Type} {n : Nat} {t : Tm Head n}
    (h : Bidirectional .synth t) : ∀ a b, t ≠ .pair a b := by
  intro a b hEq; subst hEq; cases h

theorem Bidirectional.synth_not_refl {Head : Type} {n : Nat} {t : Tm Head n}
    (h : Bidirectional .synth t) : ∀ x, t ≠ .refl x := by
  intro x hEq; subst hEq; cases h

/-! ### Simulation Completeness of `nbeBelow`, `nbeSynth`, and `nbeCheck` -/

section GenericNbECheckingCompleteness

variable {Head L : Type} [DecidableEq Head] [LevelOrder L] (S : Setting Head L)
variable [DecidableRel S.R.headEq] [∀ head, Decidable (S.R.isUniverse head)]
variable [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R)
variable (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R)
variable (complete : AlgorithmicComplete S.R S.roles)
variable (hComp : S.R.computation = RootComputation.empty)
variable (hRoles : S.roles = fun _ => .rigid)

/-- Motive for proving completeness of `ExecutableChecking.below` (`nbeBelow`)
by induction on the algorithmic type-equality derivation `Algorithmic S.R S.roles st`
(mirroring `Algorithmic.decidesBelow` in `BelowDecidability.lean`). -/
def BelowExecComplete : AlgorithmicStatement Head → Prop
  | .types Γ A _ =>
      CtxFormed S.R Γ → IsType S.R Γ A → ∀ {B}, IsType S.R Γ B → Below S.R Γ A B →
        ∃ fuel res,
          ExecutableChecking.below S.R (nbeWhnfReducer S.R (fun _ => none)) fuel Γ A B = some res
  | .typesW Γ A' _ =>
      CtxFormed S.R Γ → IsType S.R Γ A' →
        ∀ {A B}, IsType S.R Γ A → RedTy S.R S.roles Γ A A' →
          IsType S.R Γ B → Below S.R Γ A' B →
          ∃ fuel res,
            ExecutableChecking.below S.R (nbeWhnfReducer S.R (fun _ => none)) fuel Γ A B = some res
  | _ => True

include facts roots heads algebra complete hComp hRoles

private theorem below_complete_of_typeEq {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n}
    (formed : CtxFormed S.R Γ) (eAB : TypeEq S.R Γ A B) :
    ∃ fuel res,
      ExecutableChecking.below S.R (nbeWhnfReducer S.R (fun _ => none)) fuel Γ A B = some res := by
  have hAlg : Algorithmic S.R S.roles (.types Γ A B) :=
    AlgorithmicComplete.types complete eAB formed
  obtain ⟨fuel, c, hTypes⟩ :=
    nbeCompareTypes_complete_of_algorithmic (S := S) facts roots heads algebra hComp hRoles formed hAlg
  have hTypes1 := nbeCompareTypes_mono_eq S.R (fun _ => none) (Nat.le_succ fuel) hTypes
  obtain ⟨res, hBelow⟩ := below_of_types S.R (fun _ => none) hTypes1
  exact ⟨fuel + 1, res, hBelow⟩

private theorem below_complete_of_rigid {n : Nat} {Γ : Ctx Head n} {A A' B : Tm Head n}
    (shape : RigidShape S.R S.roles Γ A') (formed : CtxFormed S.R Γ)
    (rA : RedTy S.R S.roles Γ A A') (le' : Below S.R Γ A' B) :
    ∃ fuel res,
      ExecutableChecking.below S.R (nbeWhnfReducer S.R (fun _ => none)) fuel Γ A B = some res := by
  have eA'B : TypeEq S.R Γ A' B := (RigidShape.below_iff facts shape formed).1 le'
  exact below_complete_of_typeEq S facts roots heads algebra complete hComp hRoles
    formed (TypeEq.trans S.levels rA.typeEq eA'B)

/-- Every `Algorithmic` derivation witnesses simulation completeness of `ExecutableChecking.below`. -/
theorem Algorithmic.below_executable_complete {st : AlgorithmicStatement Head}
    (derivation : Algorithmic S.R S.roles st) :
    BelowExecComplete S st := by
  induction derivation with
  | types rA _ _ _ _ ih =>
      intro formed typeA B typeB le
      have le' : Below S.R _ _ B := .subTrans (TypeEq.below (TypeEq.symm rA.typeEq)) le
      exact ih formed rA.targetType typeA rA typeB le'
  | @heads n Γ h h' u _ _ _ _ =>
      intro formed typeA' A B typeA rA typeB le'
      rcases S.levels.universe_decided h with hh | nh
      · obtain ⟨v, hv, eB, c⟩ := (Below.universe_iff facts algebra formed hh).1 le'
        obtain ⟨v₀, rB, hv₀⟩ := IsType.universe_whnf facts formed typeB hv eB
        have eVV₀ : TypeEq S.R Γ (.head v) (.head v₀) :=
          TypeEq.trans S.levels (TypeEq.symm eB) rB.typeEq
        have c₀ : S.R.cumulative h v₀ :=
          algebra.same_right c (TypeEq.head_injective facts eVV₀ formed)
        obtain ⟨fA, nA, hNA, hValA⟩ := nbeWhnf_complete_of_whRed hComp hRoles rA.red (head_whnf S.shape _)
        obtain ⟨fB, nB, hNB, hValB⟩ := nbeWhnf_complete_of_whRed hComp hRoles rB.red (head_whnf S.shape _)
        let f := Nat.max fA fB
        have hNA' := nbeWhnfReducer_mono_eq S.R (fun _ => none)
          (Nat.le_trans (Nat.le_max_left fA fB) (Nat.le_succ f)) hNA
        have hNB' := nbeWhnfReducer_mono_eq S.R (fun _ => none)
          (Nat.le_trans (Nat.le_max_right fA fB) (Nat.le_succ f)) hNB
        obtain ⟨res, hBelow⟩ :=
          below_of_universes S.R (fun _ => none) hNA' hValA hNB' hValB c₀
        exact ⟨f + 1, res, hBelow⟩
      · exact below_complete_of_rigid S facts roots heads algebra complete hComp hRoles
          (.head nh) formed rA le'
  | @pi n Γ A₁ A₁' B₁ B₁' isA₁ _ _ _ ihB =>
      intro formed typePi A B typeA rA typeB le'
      have formedA₁ : CtxFormed S.R (.snoc Γ A₁) := .snoc formed isA₁
      obtain ⟨_, isB₁⟩ := IsType.pi_parts typePi
      obtain ⟨A₂, B₂, eB, eDom, leCod⟩ := (Below.pi_iff facts formed typePi).1 le'
      rcases IsType.pi_or facts formed typeB with ⟨A₂', B₂', rB⟩ | notPi
      · obtain ⟨eDom₂, eCod₂⟩ := TypeEq.pi_injective facts
          (TypeEq.trans S.levels (TypeEq.symm rB.typeEq) eB) formed
        have eA₁A₂' : TypeEq S.R Γ A₁ A₂' :=
          TypeEq.trans S.levels eDom (TypeEq.symm eDom₂)
        have leB₁B₂' : Below S.R (.snoc Γ A₁) B₁ B₂' :=
          .subTrans leCod (Below.ctxConv (TypeEq.below (TypeEq.symm eCod₂)) (TypeEq.symm eA₁A₂'))
        obtain ⟨_, ⟨u₂', hu₂', tB₂'⟩⟩ := IsType.pi_parts rB.targetType
        have isB₂' : IsType S.R (.snoc Γ A₁) B₂' :=
          ⟨u₂', hu₂', Typed.ctxBelow tB₂' (TypeEq.below eA₁A₂')⟩
        obtain ⟨fA, nA, hNA, hValA⟩ := nbeWhnf_complete_of_whRed hComp hRoles rA.red (pi_whnf S.shape _ _)
        obtain ⟨fB, nB, hNB, hValB⟩ := nbeWhnf_complete_of_whRed hComp hRoles rB.red (pi_whnf S.shape _ _)
        have hAlgDom : Algorithmic S.R S.roles (.types Γ A₁ A₂') :=
          AlgorithmicComplete.types complete eA₁A₂' formed
        obtain ⟨fDom, dDom, hDom⟩ :=
          nbeCompareTypes_complete_of_algorithmic (S := S) facts roots heads algebra hComp hRoles formed hAlgDom
        obtain ⟨fCod, dCod, hCod⟩ := ihB formedA₁ isB₁ isB₂' leB₁B₂'
        let f := Nat.max (Nat.max fA fB) (Nat.max fDom fCod)
        have hfA : fA ≤ f := Nat.le_trans (Nat.le_max_left fA fB) (Nat.le_max_left _ _)
        have hfB : fB ≤ f := Nat.le_trans (Nat.le_max_right fA fB) (Nat.le_max_left _ _)
        have hfDom : fDom ≤ f := Nat.le_trans (Nat.le_max_left fDom fCod) (Nat.le_max_right _ _)
        have hfCod : fCod ≤ f := Nat.le_trans (Nat.le_max_right fDom fCod) (Nat.le_max_right _ _)
        have hNA' := nbeWhnfReducer_mono_eq S.R (fun _ => none) (Nat.le_trans hfA (Nat.le_succ f)) hNA
        have hNB' := nbeWhnfReducer_mono_eq S.R (fun _ => none) (Nat.le_trans hfB (Nat.le_succ f)) hNB
        have hDom' := nbeCompareTypes_mono_eq S.R (fun _ => none) hfDom hDom
        have hCod' := nbeBelow_mono_eq S.R (fun _ => none) hfCod hCod
        obtain ⟨res, hBelow⟩ :=
          below_of_pi S.R (fun _ => none) hNA' hValA hNB' hValB hDom' hCod'
        exact ⟨f + 1, res, hBelow⟩
      · exact absurd eB (notPi A₂ B₂)
  | @sigma n Γ A₁ A₁' B₁ B₁' isA₁ _ _ ihA ihB =>
      intro formed typeSigma A B typeA rA typeB le'
      have formedA₁ : CtxFormed S.R (.snoc Γ A₁) := .snoc formed isA₁
      obtain ⟨_, isB₁⟩ := IsType.sigma_parts typeSigma
      obtain ⟨A₂, B₂, eB, leDom, leCod⟩ := (Below.sigma_iff facts formed typeSigma).1 le'
      rcases IsType.sigma_or facts formed typeB with ⟨A₂', B₂', rB⟩ | notSigma
      · obtain ⟨eDom₂, eCod₂⟩ := TypeEq.sigma_injective facts
          (TypeEq.trans S.levels (TypeEq.symm rB.typeEq) eB) formed
        have leA₁A₂' : Below S.R Γ A₁ A₂' :=
          .subTrans leDom (TypeEq.below (TypeEq.symm eDom₂))
        have leB₁B₂' : Below S.R (.snoc Γ A₁) B₁ B₂' :=
          .subTrans leCod (Below.ctxBelow (TypeEq.below (TypeEq.symm eCod₂)) leA₁A₂')
        obtain ⟨isA₂', ⟨u₂', hu₂', tB₂'⟩⟩ := IsType.sigma_parts rB.targetType
        have isB₂' : IsType S.R (.snoc Γ A₁) B₂' :=
          ⟨u₂', hu₂', Typed.ctxBelow tB₂' leA₁A₂'⟩
        obtain ⟨fA, nA, hNA, hValA⟩ := nbeWhnf_complete_of_whRed hComp hRoles rA.red (sigma_whnf S.shape _ _)
        obtain ⟨fB, nB, hNB, hValB⟩ := nbeWhnf_complete_of_whRed hComp hRoles rB.red (sigma_whnf S.shape _ _)
        obtain ⟨fDom, dDom, hDom⟩ := ihA formed isA₁ isA₂' leA₁A₂'
        obtain ⟨fCod, dCod, hCod⟩ := ihB formedA₁ isB₁ isB₂' leB₁B₂'
        let f := Nat.max (Nat.max fA fB) (Nat.max fDom fCod)
        have hfA : fA ≤ f := Nat.le_trans (Nat.le_max_left fA fB) (Nat.le_max_left _ _)
        have hfB : fB ≤ f := Nat.le_trans (Nat.le_max_right fA fB) (Nat.le_max_left _ _)
        have hfDom : fDom ≤ f := Nat.le_trans (Nat.le_max_left fDom fCod) (Nat.le_max_right _ _)
        have hfCod : fCod ≤ f := Nat.le_trans (Nat.le_max_right fDom fCod) (Nat.le_max_right _ _)
        have hNA' := nbeWhnfReducer_mono_eq S.R (fun _ => none) (Nat.le_trans hfA (Nat.le_succ f)) hNA
        have hNB' := nbeWhnfReducer_mono_eq S.R (fun _ => none) (Nat.le_trans hfB (Nat.le_succ f)) hNB
        have hDom' := nbeBelow_mono_eq S.R (fun _ => none) hfDom hDom
        have hCod' := nbeBelow_mono_eq S.R (fun _ => none) hfCod hCod
        obtain ⟨res, hBelow⟩ :=
          below_of_sigma S.R (fun _ => none) hNA' hValA hNB' hValB hDom' hCod'
        exact ⟨f + 1, res, hBelow⟩
      · exact absurd eB (notSigma A₂ B₂)
  | id _ _ _ _ _ _ =>
      intro formed _ A B _ rA _ le'
      exact below_complete_of_rigid S facts roots heads algebra complete hComp hRoles
        .id formed rA le'
  | inductiveType role _ =>
      intro formed _ A B _ rA _ le'
      exact below_complete_of_rigid S facts roots heads algebra complete hComp hRoles
        (.inductiveType role) formed rA le'
  | neutralTypes nA _ _ _ _ =>
      intro formed _ A B _ rA _ le'
      exact below_complete_of_rigid S facts roots heads algebra complete hComp hRoles
        (.neutral nA) formed rA le'
  | terms => trivial
  | univ => trivial
  | eta => trivial
  | sigmaEta => trivial
  | refl => trivial
  | spine => trivial
  | var => trivial
  | const => trivial
  | app => trivial
  | fst => trivial
  | snd => trivial
  | spinesW => trivial

/-- **Completeness of `nbeBelow`**:
Whenever `Below S.R Γ A B` holds between well-formed types `A` and `B` in a formed
context `Γ`, there exists a finite fuel at which `nbeBelow` succeeds. -/
theorem nbeBelow_complete {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n}
    (formed : CtxFormed S.R Γ) (typeA : IsType S.R Γ A) (typeB : IsType S.R Γ B)
    (hBelow : Below S.R Γ A B) :
    ∃ fuel res,
      nbeBelow S.R (fun _ => none) fuel Γ A B = some res :=
  Algorithmic.below_executable_complete S facts roots heads algebra complete hComp hRoles
    (complete.types typeA.refl formed) formed typeA typeB hBelow

/-- Completeness of primitive head choices (`typing` and `join`) with respect to
`R.headTyping` and `R.isUniverse`. -/
structure HeadChoicesComplete (R : Rules Head)
    (choices : ExecutableChecking.HeadChoices R) : Prop where
  typing_complete : ∀ {h u : Head}, R.headTyping h u → ∃ res, choices.typing h = some res
  join_complete : ∀ {u v : Head}, R.isUniverse u → R.isUniverse v → ∃ res, choices.join u v = some res

/-- Bundled simulation completeness statement for `nbeSynth` and `nbeCheck`
on the bidirectional fragment `Bidirectional mode t`. -/
def ExecKernelComplete (choices : ExecutableChecking.HeadChoices S.R)
    (mode : Mode) {n : Nat} (t : Tm Head n) : Prop :=
  match mode with
  | .synth =>
      ∀ {Γ : Ctx Head n} {E : Tm Head n}, CtxFormed S.R Γ → Typed S.R Γ t E →
        ∃ T fuel res,
          Synth S.R S.roles Γ t T ∧
          ExecutableChecking.synth S.R choices (nbeWhnfReducer S.R (fun _ => none)) fuel Γ t = some res ∧
          res.1 = T
  | .check =>
      ∀ {Γ : Ctx Head n} {E : Tm Head n}, CtxFormed S.R Γ → Typed S.R Γ t E →
        Check S.R S.roles Γ t E ∧
        ∃ fuel res,
          ExecutableChecking.check S.R choices (nbeWhnfReducer S.R (fun _ => none)) fuel Γ t E = some res

/-- **Simulation Completeness of `nbeSynth` and `nbeCheck`**:
On the bidirectional fragment `Bidirectional mode t`, whenever `Typed S.R Γ t E`
holds in a formed context `Γ`, our closure-based NbE bidirectional typechecker
(`ExecutableChecking.synth` / `ExecutableChecking.check` with `nbeWhnfReducer`)
succeeds at some finite `fuel`. -/
theorem Bidirectional.executable_complete
    (headsTyped : ∀ {h u u' : Head}, S.R.headTyping h u → S.R.headTyping h u' → u = u')
    {choices : ExecutableChecking.HeadChoices S.R}
    (hChoices : HeadChoicesComplete S.R choices)
    {mode : Mode} {n : Nat} {t : Tm Head n}
    (fragment : Bidirectional mode t) :
    ExecKernelComplete S choices mode t := by
  have principal := fun {n : Nat} {Γ : Ctx Head n} {t T : Tm Head n}
      (synth : Synth S.R S.roles Γ t T) (formed : CtxFormed S.R Γ) =>
    Synth.principal facts algebra headsTyped synth formed
  induction fragment with
  | var i =>
      intro Γ E _ _
      exact ⟨Ctx.lookup Γ i, 1, ⟨Ctx.lookup Γ i, ⟨.var i⟩⟩, .var i, rfl, rfl⟩
  | const name =>
      intro Γ E _ typing
      obtain ⟨type, _, declared, tType, hu, _⟩ := Typed.generation typing
      refine ⟨liftClosed type, 1, ⟨liftClosed type, ⟨.const declared⟩⟩,
        .const declared tType hu, ?_, rfl⟩
      simp only [ExecutableChecking.synth]
      split
      · rename_i chosen known
        have same : chosen = type := Option.some.inj (known.symm.trans declared)
        subst chosen
        rfl
      · rename_i known
        rw [declared] at known
        contradiction
  | head h =>
      intro Γ E _ typing
      obtain ⟨_, headTyping, _⟩ := Typed.generation typing
      obtain ⟨chosen, hChosen⟩ := hChoices.typing_complete headTyping
      refine ⟨.head chosen.val, 1, ⟨.head chosen.val, ⟨.head chosen.property⟩⟩,
        .head chosen.property, ?_, rfl⟩
      simp [ExecutableChecking.synth, hChosen, bind, Option.bind, pure]
  | pi _ _ ihA ihB =>
      intro Γ E formed typing
      obtain ⟨u, v, _, tA, hu, tB, hv, _, _⟩ := Typed.generation typing
      obtain ⟨TA, fSA, rA_exec, sA, hSA, hValRA⟩ := ihA formed tA
      obtain ⟨u₀, rA, hu₀⟩ :=
        Synth.universe_whnf facts algebra headsTyped sA formed tA hu
      have formedA : CtxFormed S.R (.snoc Γ _) := .snoc formed ⟨u, hu, tA⟩
      obtain ⟨TB, fSB, rB_exec, sB, hSB, hValRB⟩ := ihB formedA tB
      obtain ⟨v₀, rB, hv₀⟩ :=
        Synth.universe_whnf facts algebra headsTyped sB formedA tB hv
      have rA' : RedTy S.R S.roles Γ rA_exec.1 (.head u₀) := hValRA ▸ rA
      have rB' : RedTy S.R S.roles (.snoc Γ _) rB_exec.1 (.head v₀) := hValRB ▸ rB
      obtain ⟨fUA, nUA, hNUA, hValUA⟩ := nbeWhnf_complete_of_whRed hComp hRoles rA'.red (head_whnf S.shape _)
      obtain ⟨uA, hUA, hValuA⟩ := asUniverse_of_whnf S.R (fun _ => none) hNUA hValUA hu₀
      obtain ⟨fUB, nUB, hNUB, hValUB⟩ := nbeWhnf_complete_of_whRed hComp hRoles rB'.red (head_whnf S.shape _)
      obtain ⟨uB, hUB, hValuB⟩ := asUniverse_of_whnf S.R (fun _ => none) hNUB hValUB hv₀
      obtain ⟨j, hJ⟩ := hChoices.join_complete uA.property.1 uB.property.1
      have hJoin₀ : S.R.join u₀ v₀ j.val := hValuA ▸ hValuB ▸ j.property
      let f := Nat.max (Nat.max fSA fSB) (Nat.max fUA fUB)
      have hfSA : fSA ≤ f := Nat.le_trans (Nat.le_max_left fSA fSB) (Nat.le_max_left _ _)
      have hfSB : fSB ≤ f := Nat.le_trans (Nat.le_max_right fSA fSB) (Nat.le_max_left _ _)
      have hfUA : fUA ≤ f + 1 :=
        Nat.le_trans (Nat.le_trans (Nat.le_max_left fUA fUB) (Nat.le_max_right _ _)) (Nat.le_succ f)
      have hfUB : fUB ≤ f + 1 :=
        Nat.le_trans (Nat.le_trans (Nat.le_max_right fUA fUB) (Nat.le_max_right _ _)) (Nat.le_succ f)
      have hSA' := nbeSynth_mono_eq S.R choices (fun _ => none) hfSA hSA
      have hSB' := nbeSynth_mono_eq S.R choices (fun _ => none) hfSB hSB
      have hUA' := asUniverse_mono_eq S.R (fun _ => none) hfUA hUA
      have hUB' := asUniverse_mono_eq S.R (fun _ => none) hfUB hUB
      obtain ⟨res, hRes, hResVal⟩ :=
        synth_pi_of S.R choices (fun _ => none) hSA' hUA' hSB' hUB' hJ
      exact ⟨.head j.val, f + 1, res, .pi sA rA hu₀ sB rB hv₀ hJoin₀, hRes, hResVal⟩
  | sigma _ _ ihA ihB =>
      intro Γ E formed typing
      obtain ⟨u, v, _, tA, hu, tB, hv, _, _⟩ := Typed.generation typing
      obtain ⟨TA, fSA, rA_exec, sA, hSA, hValRA⟩ := ihA formed tA
      obtain ⟨u₀, rA, hu₀⟩ :=
        Synth.universe_whnf facts algebra headsTyped sA formed tA hu
      have formedA : CtxFormed S.R (.snoc Γ _) := .snoc formed ⟨u, hu, tA⟩
      obtain ⟨TB, fSB, rB_exec, sB, hSB, hValRB⟩ := ihB formedA tB
      obtain ⟨v₀, rB, hv₀⟩ :=
        Synth.universe_whnf facts algebra headsTyped sB formedA tB hv
      have rA' : RedTy S.R S.roles Γ rA_exec.1 (.head u₀) := hValRA ▸ rA
      have rB' : RedTy S.R S.roles (.snoc Γ _) rB_exec.1 (.head v₀) := hValRB ▸ rB
      obtain ⟨fUA, nUA, hNUA, hValUA⟩ := nbeWhnf_complete_of_whRed hComp hRoles rA'.red (head_whnf S.shape _)
      obtain ⟨uA, hUA, hValuA⟩ := asUniverse_of_whnf S.R (fun _ => none) hNUA hValUA hu₀
      obtain ⟨fUB, nUB, hNUB, hValUB⟩ := nbeWhnf_complete_of_whRed hComp hRoles rB'.red (head_whnf S.shape _)
      obtain ⟨uB, hUB, hValuB⟩ := asUniverse_of_whnf S.R (fun _ => none) hNUB hValUB hv₀
      obtain ⟨j, hJ⟩ := hChoices.join_complete uA.property.1 uB.property.1
      have hJoin₀ : S.R.join u₀ v₀ j.val := hValuA ▸ hValuB ▸ j.property
      let f := Nat.max (Nat.max fSA fSB) (Nat.max fUA fUB)
      have hfSA : fSA ≤ f := Nat.le_trans (Nat.le_max_left fSA fSB) (Nat.le_max_left _ _)
      have hfSB : fSB ≤ f := Nat.le_trans (Nat.le_max_right fSA fSB) (Nat.le_max_left _ _)
      have hfUA : fUA ≤ f + 1 :=
        Nat.le_trans (Nat.le_trans (Nat.le_max_left fUA fUB) (Nat.le_max_right _ _)) (Nat.le_succ f)
      have hfUB : fUB ≤ f + 1 :=
        Nat.le_trans (Nat.le_trans (Nat.le_max_right fUA fUB) (Nat.le_max_right _ _)) (Nat.le_succ f)
      have hSA' := nbeSynth_mono_eq S.R choices (fun _ => none) hfSA hSA
      have hSB' := nbeSynth_mono_eq S.R choices (fun _ => none) hfSB hSB
      have hUA' := asUniverse_mono_eq S.R (fun _ => none) hfUA hUA
      have hUB' := asUniverse_mono_eq S.R (fun _ => none) hfUB hUB
      obtain ⟨res, hRes, hResVal⟩ :=
        synth_sigma_of S.R choices (fun _ => none) hSA' hUA' hSB' hUB' hJ
      exact ⟨.head j.val, f + 1, res, .sigma sA rA hu₀ sB rB hv₀ hJoin₀, hRes, hResVal⟩
  | id _ _ _ ihA iha ihb =>
      intro Γ E formed typing
      obtain ⟨u, tA, hu, ta, tb, _⟩ := Typed.generation typing
      obtain ⟨TA, fSA, rA_exec, sA, hSA, hValRA⟩ := ihA formed tA
      obtain ⟨u₀, rA, hu₀⟩ :=
        Synth.universe_whnf facts algebra headsTyped sA formed tA hu
      obtain ⟨ca_k, fCA, rCA, hCA⟩ := iha formed ta
      obtain ⟨cb_k, fCB, rCB, hCB⟩ := ihb formed tb
      have rA' : RedTy S.R S.roles Γ rA_exec.1 (.head u₀) := hValRA ▸ rA
      obtain ⟨fUA, nUA, hNUA, hValUA⟩ := nbeWhnf_complete_of_whRed hComp hRoles rA'.red (head_whnf S.shape _)
      obtain ⟨uA, hUA, hValuA⟩ := asUniverse_of_whnf S.R (fun _ => none) hNUA hValUA hu₀
      let f := Nat.max (Nat.max fSA fUA) (Nat.max fCA fCB)
      have hfSA : fSA ≤ f := Nat.le_trans (Nat.le_max_left fSA fUA) (Nat.le_max_left _ _)
      have hfUA : fUA ≤ f + 1 :=
        Nat.le_trans (Nat.le_trans (Nat.le_max_right fSA fUA) (Nat.le_max_left _ _)) (Nat.le_succ f)
      have hfCA : fCA ≤ f := Nat.le_trans (Nat.le_max_left fCA fCB) (Nat.le_max_right _ _)
      have hfCB : fCB ≤ f := Nat.le_trans (Nat.le_max_right fCA fCB) (Nat.le_max_right _ _)
      have hSA' := nbeSynth_mono_eq S.R choices (fun _ => none) hfSA hSA
      have hUA' := asUniverse_mono_eq S.R (fun _ => none) hfUA hUA
      have hCA' := nbeCheck_mono_eq S.R choices (fun _ => none) hfCA hCA
      have hCB' := nbeCheck_mono_eq S.R choices (fun _ => none) hfCB hCB
      obtain ⟨res, hRes, hResVal⟩ :=
        synth_id_of S.R choices (fun _ => none) hSA' hUA' hCA' hCB'
      exact ⟨.head uA.val, f + 1, res,
        .id sA (hValuA.symm ▸ rA) uA.property.1 ca_k cb_k, hRes, hResVal⟩
  | app ff _ ihf iha =>
      intro Γ E formed typing
      obtain ⟨A', B', tf, ta, _⟩ := Typed.generation typing
      obtain ⟨F, fSF, rF_exec, sf, hSF, hValRF⟩ := ihf formed tf
      obtain ⟨tF, principalF⟩ := principal sf formed
      have typePi := Typed.isType tf formed
      obtain ⟨A₁, B₁, eF, eA₁, _⟩ := Below.pi_inv facts
        (TypeLe.toBelow (principalF tf) typePi) formed (IsType.refl typePi)
      rcases IsType.pi_or facts formed (Typed.isType tF formed) with
        ⟨A₀, B₀, red⟩ | notPi
      · obtain ⟨e₀₁, _⟩ := TypeEq.pi_injective facts
          (TypeEq.trans S.levels (TypeEq.symm red.typeEq) eF) formed
        have ta₀ : Typed S.R Γ _ A₀ :=
          Typed.convType ta (TypeEq.symm (TypeEq.trans S.levels e₀₁ eA₁))
        obtain ⟨ca_k, fCA, rCA, hCA⟩ := iha formed ta₀
        have red' : RedTy S.R S.roles Γ rF_exec.1 (.pi A₀ B₀) := hValRF ▸ red
        obtain ⟨fNF, nF, hNF, hValF⟩ := nbeWhnf_complete_of_whRed hComp hRoles red'.red (pi_whnf S.shape _ _)
        let f := Nat.max (Nat.max fSF fCA) fNF
        have hfSF : fSF ≤ f := Nat.le_trans (Nat.le_max_left fSF fCA) (Nat.le_max_left _ _)
        have hfCA : fCA ≤ f := Nat.le_trans (Nat.le_max_right fSF fCA) (Nat.le_max_left _ _)
        have hfNF : fNF ≤ f + 1 := Nat.le_trans (Nat.le_max_right _ _) (Nat.le_succ f)
        have hSF' := nbeSynth_mono_eq S.R choices (fun _ => none) hfSF hSF
        have hCA' := nbeCheck_mono_eq S.R choices (fun _ => none) hfCA hCA
        have hNF' := nbeWhnfReducer_mono_eq S.R (fun _ => none) hfNF hNF
        obtain ⟨res, hRes, hResVal⟩ :=
          synth_app_of S.R choices (fun _ => none) (Bidirectional.synth_not_lam ff) hSF' hNF' hValF hCA'
        exact ⟨inst0 _ B₀, f + 1, res, .app sf red ca_k, hRes, hResVal⟩
      · exact absurd eF (notPi A₁ B₁)
  | fst _ ihp =>
      intro Γ E formed typing
      obtain ⟨A', B', tp, _⟩ := Typed.generation typing
      obtain ⟨P, fSP, rP_exec, sp, hSP, hValRP⟩ := ihp formed tp
      obtain ⟨tP, principalP⟩ := principal sp formed
      have typeSigma := Typed.isType tp formed
      obtain ⟨A₁, B₁, eP, _, _⟩ := Below.sigma_inv facts
        (TypeLe.toBelow (principalP tp) typeSigma) formed (IsType.refl typeSigma)
      rcases IsType.sigma_or facts formed (Typed.isType tP formed) with
        ⟨A₀, B₀, red⟩ | notSigma
      · have red' : RedTy S.R S.roles Γ rP_exec.1 (.sigma A₀ B₀) := hValRP ▸ red
        obtain ⟨fNP, nP, hNP, hValP⟩ := nbeWhnf_complete_of_whRed hComp hRoles red'.red (sigma_whnf S.shape _ _)
        let f := Nat.max fSP fNP
        have hfSP : fSP ≤ f := Nat.le_max_left fSP fNP
        have hfNP : fNP ≤ f + 1 := Nat.le_trans (Nat.le_max_right fSP fNP) (Nat.le_succ f)
        have hSP' := nbeSynth_mono_eq S.R choices (fun _ => none) hfSP hSP
        have hNP' := nbeWhnfReducer_mono_eq S.R (fun _ => none) hfNP hNP
        obtain ⟨res, hRes, hResVal⟩ :=
          synth_fst_of S.R choices (fun _ => none) hSP' hNP' hValP
        exact ⟨A₀, f + 1, res, .fst sp red, hRes, hResVal⟩
      · exact absurd eP (notSigma A₁ B₁)
  | snd _ ihp =>
      intro Γ E formed typing
      obtain ⟨A', B', tp, _⟩ := Typed.generation typing
      obtain ⟨P, fSP, rP_exec, sp, hSP, hValRP⟩ := ihp formed tp
      obtain ⟨tP, principalP⟩ := principal sp formed
      have typeSigma := Typed.isType tp formed
      obtain ⟨A₁, B₁, eP, _, _⟩ := Below.sigma_inv facts
        (TypeLe.toBelow (principalP tp) typeSigma) formed (IsType.refl typeSigma)
      rcases IsType.sigma_or facts formed (Typed.isType tP formed) with
        ⟨A₀, B₀, red⟩ | notSigma
      · have red' : RedTy S.R S.roles Γ rP_exec.1 (.sigma A₀ B₀) := hValRP ▸ red
        obtain ⟨fNP, nP, hNP, hValP⟩ := nbeWhnf_complete_of_whRed hComp hRoles red'.red (sigma_whnf S.shape _ _)
        let f := Nat.max fSP fNP
        have hfSP : fSP ≤ f := Nat.le_max_left fSP fNP
        have hfNP : fNP ≤ f + 1 := Nat.le_trans (Nat.le_max_right fSP fNP) (Nat.le_succ f)
        have hSP' := nbeSynth_mono_eq S.R choices (fun _ => none) hfSP hSP
        have hNP' := nbeWhnfReducer_mono_eq S.R (fun _ => none) hfNP hNP
        obtain ⟨res, hRes, hResVal⟩ :=
          synth_snd_of S.R choices (fun _ => none) hSP' hNP' hValP
        exact ⟨inst0 (.fst _) B₀, f + 1, res, .snd sp red, hRes, hResVal⟩
      · exact absurd eP (notSigma A₁ B₁)
  | redex _ _ ihb iha =>
      intro Γ E formed typing
      obtain ⟨A', B', tLam, ta, _⟩ := Typed.generation typing
      obtain ⟨A'', B'', _, _, _, tb, lePi⟩ := Typed.generation tLam
      obtain ⟨TA, fSA, rA_exec, sa, hSA, hValRA⟩ := iha formed ta
      obtain ⟨tTA, principalA⟩ := principal sa formed
      have isTA := Typed.isType tTA formed
      obtain ⟨e₁, _⟩ := TypeLe.pi_parts facts lePi
        (Typed.isType tLam formed) formed
      have le : Below S.R Γ rA_exec.1 A'' :=
        hValRA.symm ▸ .subTrans (TypeLe.toBelow (principalA ta)
          (Typed.isType ta formed)) (TypeEq.below (TypeEq.symm e₁))
      have isRA : IsType S.R Γ rA_exec.1 := hValRA.symm ▸ isTA
      obtain ⟨TB, fSB, rB_exec, sb, hSB, hValRB⟩ :=
        ihb (.snoc formed isRA) (Typed.ctxBelow tb le)
      let f := Nat.max fSA fSB
      have hSA' := nbeSynth_mono_eq S.R choices (fun _ => none) (Nat.le_max_left fSA fSB) hSA
      have hSB' := nbeSynth_mono_eq S.R choices (fun _ => none) (Nat.le_max_right fSA fSB) hSB
      obtain ⟨res, hRes, hResVal⟩ :=
        synth_redex_of S.R choices (fun _ => none) hSA' hSB'
      exact ⟨inst0 _ TB, f + 1, res,
        .redex sa (hValRA ▸ IsType.refl isRA) sb,
        hRes, hResVal.trans (congrArg (inst0 _) hValRB)⟩
  | lam _ ihb =>
      intro Γ E formed typing
      obtain ⟨A, B, u, tPi, hu, tb, le⟩ := Typed.generation typing
      have isE := Typed.isType typing formed
      have leE := TypeLe.toBelow le isE
      obtain ⟨A₂, B₂, eE, eA, leB⟩ :=
        Below.pi_source facts leE formed (IsType.refl ⟨u, hu, tPi⟩)
      rcases IsType.pi_or facts formed isE with ⟨A₁, B₁, red⟩ | notPi
      · obtain ⟨e₁₂, eB₁₂⟩ := TypeEq.pi_injective facts
          (TypeEq.trans S.levels (TypeEq.symm red.typeEq) eE) formed
        have eA₁ : TypeEq S.R Γ A A₁ := TypeEq.trans S.levels eA (TypeEq.symm e₁₂)
        have tb₁ : Typed S.R (.snoc Γ A₁) _ B₁ := Typed.convType
          (Typed.ctxBelow (.sub tb leB) (TypeEq.below (TypeEq.symm eA₁))) (TypeEq.symm eB₁₂)
        obtain ⟨isA₁, _⟩ := IsType.pi_parts red.targetType
        obtain ⟨cb_k, fCB, rCB, hCB⟩ := ihb (.snoc formed isA₁) tb₁
        obtain ⟨fNE, nE, hNE, hValE⟩ := nbeWhnf_complete_of_whRed hComp hRoles red.red (pi_whnf S.shape _ _)
        let f := Nat.max fCB fNE
        have hCB' := nbeCheck_mono_eq S.R choices (fun _ => none) (Nat.le_max_left fCB fNE) hCB
        have hNE' := nbeWhnfReducer_mono_eq S.R (fun _ => none)
          (Nat.le_trans (Nat.le_max_right fCB fNE) (Nat.le_succ f)) hNE
        obtain ⟨res, hRes⟩ := check_lam_of S.R choices (fun _ => none) hNE' hValE hCB'
        exact ⟨.lamCheck red cb_k, f + 1, res, hRes⟩
      · exact absurd eE (notPi A₂ B₂)
  | pair _ _ iha ihb =>
      intro Γ E formed typing
      obtain ⟨A, B, u, tSigma, hu, ta, tb, le⟩ := Typed.generation typing
      have isE := Typed.isType typing formed
      have leE := TypeLe.toBelow le isE
      obtain ⟨A₂, B₂, eE, leA, leB⟩ :=
        Below.sigma_source facts leE formed (IsType.refl ⟨u, hu, tSigma⟩)
      rcases IsType.sigma_or facts formed isE with ⟨A₁, B₁, red⟩ | notSigma
      · obtain ⟨e₁₂, eB₁₂⟩ := TypeEq.sigma_injective facts
          (TypeEq.trans S.levels (TypeEq.symm red.typeEq) eE) formed
        have ta₁ : Typed S.R Γ _ A₁ := Typed.convType (.sub ta leA) (TypeEq.symm e₁₂)
        have tb₁ : Typed S.R Γ _ (inst0 _ B₁) := Typed.convType
          (.sub tb (Derivable.substitutes leB (SubstMor.single ta)))
          (TypeEq.symm (TypeEq.instantiate eB₁₂ ta₁))
        obtain ⟨ca_k, fCA, rCA, hCA⟩ := iha formed ta₁
        obtain ⟨cb_k, fCB, rCB, hCB⟩ := ihb formed tb₁
        obtain ⟨fNE, nE, hNE, hValE⟩ := nbeWhnf_complete_of_whRed hComp hRoles red.red (sigma_whnf S.shape _ _)
        let f := Nat.max (Nat.max fCA fCB) fNE
        have hfCA : fCA ≤ f := Nat.le_trans (Nat.le_max_left fCA fCB) (Nat.le_max_left _ _)
        have hfCB : fCB ≤ f := Nat.le_trans (Nat.le_max_right fCA fCB) (Nat.le_max_left _ _)
        have hfNE : fNE ≤ f + 1 := Nat.le_trans (Nat.le_max_right _ _) (Nat.le_succ f)
        have hCA' := nbeCheck_mono_eq S.R choices (fun _ => none) hfCA hCA
        have hCB' := nbeCheck_mono_eq S.R choices (fun _ => none) hfCB hCB
        have hNE' := nbeWhnfReducer_mono_eq S.R (fun _ => none) hfNE hNE
        obtain ⟨res, hRes⟩ := check_pair_of S.R choices (fun _ => none) hNE' hValE hCA' hCB'
        exact ⟨.pairCheck red ca_k cb_k, f + 1, res, hRes⟩
      · exact absurd eE (notSigma A₂ B₂)
  | refl _ ihx =>
      intro Γ E formed typing
      obtain ⟨A, tx, le⟩ := Typed.generation typing
      have isE := Typed.isType typing formed
      have eE := TypeLe.id_eq facts le isE formed
      rcases IsType.id_or facts formed isE with ⟨C, a, b, red⟩ | notId
      · obtain ⟨eA, ea, eb⟩ := TypeEq.id_injective facts
          (TypeEq.trans S.levels eE red.typeEq) formed
        have txC : Typed S.R Γ _ C := Typed.convType tx eA
        have eaC : Equal S.R Γ _ a C := Equal.convType ea eA
        have ebC : Equal S.R Γ _ b C := Equal.convType eb eA
        obtain ⟨cx_k, fCX, rCX, hCX⟩ := ihx formed txC
        obtain ⟨fNE, nE, hNE, hValE⟩ := nbeWhnf_complete_of_whRed hComp hRoles red.red (id_whnf S.shape _ _ _)
        have hAlgA : Algorithmic S.R S.roles (.terms Γ _ a C) :=
          complete formed eaC
        have hAlgB : Algorithmic S.R S.roles (.terms Γ _ b C) :=
          complete formed ebC
        obtain ⟨fCXA, cxa, hCXA⟩ :=
          nbeCompare_complete_of_algorithmic (S := S) facts roots heads algebra hComp hRoles formed hAlgA
        obtain ⟨fCXB, cxb, hCXB⟩ :=
          nbeCompare_complete_of_algorithmic (S := S) facts roots heads algebra hComp hRoles formed hAlgB
        let f := Nat.max (Nat.max fCX fNE) (Nat.max fCXA fCXB)
        have hfCX : fCX ≤ f := Nat.le_trans (Nat.le_max_left fCX fNE) (Nat.le_max_left _ _)
        have hfNE : fNE ≤ f + 1 :=
          Nat.le_trans (Nat.le_trans (Nat.le_max_right fCX fNE) (Nat.le_max_left _ _)) (Nat.le_succ f)
        have hfCXA : fCXA ≤ f := Nat.le_trans (Nat.le_max_left fCXA fCXB) (Nat.le_max_right _ _)
        have hfCXB : fCXB ≤ f := Nat.le_trans (Nat.le_max_right fCXA fCXB) (Nat.le_max_right _ _)
        have hCX' := nbeCheck_mono_eq S.R choices (fun _ => none) hfCX hCX
        have hNE' := nbeWhnfReducer_mono_eq S.R (fun _ => none) hfNE hNE
        have hCXA' := nbeCompare_mono_eq S.R (fun _ => none) hfCXA hCXA
        have hCXB' := nbeCompare_mono_eq S.R (fun _ => none) hfCXB hCXB
        obtain ⟨res, hRes⟩ :=
          check_refl_of S.R choices (fun _ => none) hNE' hValE hCX' hCXA' hCXB'
        exact ⟨.reflCheck red cx_k eaC ebC, f + 1, res, hRes⟩
      · exact absurd (TypeEq.symm eE) (notId _ _ _)
  | synthesized ft iht =>
      intro Γ E formed typing
      obtain ⟨T, fST, rT_exec, s, hST, hValRT⟩ := iht formed typing
      have hBelow : Below S.R Γ T E :=
        TypeLe.toBelow ((principal s formed).2 typing) (Typed.isType typing formed)
      have isT : IsType S.R Γ rT_exec.1 :=
        hValRT.symm ▸ Typed.isType (principal s formed).1 formed
      have isE : IsType S.R Γ E := Typed.isType typing formed
      have hBelow' : Below S.R Γ rT_exec.1 E := hValRT.symm ▸ hBelow
      obtain ⟨fB, u, hB⟩ :=
        nbeBelow_complete S facts roots heads algebra complete hComp hRoles formed isT isE hBelow'
      let f := Nat.max fST fB
      have hST' := nbeSynth_mono_eq S.R choices (fun _ => none) (Nat.le_max_left fST fB) hST
      have hB' := nbeBelow_mono_eq S.R (fun _ => none) (Nat.le_max_right fST fB) hB
      obtain ⟨res, hRes⟩ :=
        check_switch_of S.R choices (fun _ => none)
          (Bidirectional.synth_not_lam ft)
          (Bidirectional.synth_not_pair ft)
          (Bidirectional.synth_not_refl ft)
          hST' hB'
      exact ⟨.switch s hBelow, f + 1, res, hRes⟩

/-- Contexts whose domain types all lie in the bidirectional synthesis fragment. -/
inductive BidirectionalCtx {Head : Type} : {n : Nat} → Ctx Head n → Prop where
  | nil : BidirectionalCtx .nil
  | snoc {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} :
      BidirectionalCtx Γ → Bidirectional .synth A → BidirectionalCtx (.snoc Γ A)

/-- Simulation completeness of `nbeFormContext` on `BidirectionalCtx`. -/
theorem nbeFormContext_complete
    (headsTyped : ∀ {h u u' : Head}, S.R.headTyping h u → S.R.headTyping h u' → u = u')
    {choices : ExecutableChecking.HeadChoices S.R}
    (hChoices : HeadChoicesComplete S.R choices)
    {n : Nat} {Γ : Ctx Head n}
    (hΓ : BidirectionalCtx Γ) (formed : CtxFormed S.R Γ) :
    ∃ fuel res,
      nbeFormContext S.R choices (fun _ => none) fuel Γ = some res := by
  induction hΓ with
  | nil => exact ⟨0, ⟨.nil⟩, rfl⟩
  | @snoc m ctx dom _ fDom ih =>
      cases formed with
      | snoc formedCtx isDom =>
          rcases isDom with ⟨u, hu, tDom⟩
          obtain ⟨fCtx, rCtx, hCtx⟩ := ih formedCtx
          obtain ⟨TDom, fSDom, rDom_exec, sDom, hSDom, hValDom⟩ :=
            Bidirectional.executable_complete S facts roots heads algebra complete hComp hRoles
              headsTyped hChoices fDom formedCtx tDom
          obtain ⟨u₀, rDom, hu₀⟩ :=
            Synth.universe_whnf facts algebra headsTyped sDom formedCtx tDom hu
          have rDom' : RedTy S.R S.roles ctx rDom_exec.1 (.head u₀) := hValDom ▸ rDom
          obtain ⟨fUDom, nUDom, hNUDom, hValUDom⟩ :=
            nbeWhnf_complete_of_whRed hComp hRoles rDom'.red (head_whnf S.shape _)
          obtain ⟨uDom, hUDom, _⟩ :=
            asUniverse_of_whnf S.R (fun _ => none) hNUDom hValUDom hu₀
          let f := Nat.max fCtx (Nat.max fSDom fUDom)
          have hfCtx : fCtx ≤ f := Nat.le_max_left _ _
          have hfSDom : fSDom ≤ f := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
          have hfUDom : fUDom ≤ f := Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
          have hCtx' := nbeFormContext_mono_eq S.R choices (fun _ => none) hfCtx hCtx
          have hSDom' := nbeSynth_mono_eq S.R choices (fun _ => none) hfSDom hSDom
          have hUDom' := asUniverse_mono_eq S.R (fun _ => none) hfUDom hUDom
          refine ⟨f, ⟨.snoc rCtx.down rDom_exec.2.down uDom.property.2 uDom.property.1⟩, ?_⟩
          unfold nbeFormContext ExecutableChecking.formContext
          change (do
            let previous ← nbeFormContext S.R choices (fun _ => none) f ctx
            let inferred ← nbeSynth S.R choices (fun _ => none) f ctx dom
            let level ← ExecutableChecking.asUniverse S.R (nbeWhnfReducer S.R (fun _ => none)) f inferred.1
            pure (⟨.snoc previous.down inferred.2.down level.property.2 level.property.1⟩ :
              PLift (ExecutableChecking.ContextAlgorithm S.R (.snoc ctx dom)))) = _
          simp [hCtx', hSDom', hUDom', bind, Option.bind, pure]

/-- Simulation completeness of `nbeJudgment` (`nbeAccepts`) on the bidirectional fragment. -/
theorem nbeJudgment_complete
    (headsTyped : ∀ {h u u' : Head}, S.R.headTyping h u → S.R.headTyping h u' → u = u')
    {choices : ExecutableChecking.HeadChoices S.R}
    (hChoices : HeadChoicesComplete S.R choices)
    {n : Nat} {Γ : Ctx Head n} {t E : Tm Head n}
    (hΓ : BidirectionalCtx Γ) (hE : Bidirectional .synth E) (ht : Bidirectional .check t)
    (formed : CtxFormed S.R Γ) (typing : Typed S.R Γ t E) :
    ∃ fuel cert,
      nbeJudgment S.R choices (fun _ => none) fuel Γ t E = some cert := by
  obtain ⟨fCtx, rCtx, hCtx⟩ :=
    nbeFormContext_complete S facts roots heads algebra complete hComp hRoles
      headsTyped hChoices hΓ formed
  obtain ⟨u, hu, tE⟩ := Typed.isType typing formed
  obtain ⟨TE, fSE, rE_exec, sE, hSE, hValE⟩ :=
    Bidirectional.executable_complete S facts roots heads algebra complete hComp hRoles
      headsTyped hChoices hE formed tE
  obtain ⟨u₀, rE, hu₀⟩ :=
    Synth.universe_whnf facts algebra headsTyped sE formed tE hu
  have rE' : RedTy S.R S.roles Γ rE_exec.1 (.head u₀) := hValE ▸ rE
  obtain ⟨fUE, nUE, hNUE, hValUE⟩ :=
    nbeWhnf_complete_of_whRed hComp hRoles rE'.red (head_whnf S.shape _)
  obtain ⟨uE, hUE, _⟩ :=
    asUniverse_of_whnf S.R (fun _ => none) hNUE hValUE hu₀
  obtain ⟨_, fCt, rCt, hCt⟩ :=
    Bidirectional.executable_complete S facts roots heads algebra complete hComp hRoles
      headsTyped hChoices ht formed typing
  let f := Nat.max (Nat.max fCtx fSE) (Nat.max fUE fCt)
  have hfCtx : fCtx ≤ f := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have hfSE : fSE ≤ f := Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
  have hfUE : fUE ≤ f := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  have hfCt : fCt ≤ f := Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  have hCtx' := nbeFormContext_mono_eq S.R choices (fun _ => none) hfCtx hCtx
  have hSE' := nbeSynth_mono_eq S.R choices (fun _ => none) hfSE hSE
  have hUE' := asUniverse_mono_eq S.R (fun _ => none) hfUE hUE
  have hCt' := nbeCheck_mono_eq S.R choices (fun _ => none) hfCt hCt
  refine ⟨f, ⟨rCtx.down, uE.val, rE_exec.1, rE_exec.2.down, uE.property.2, uE.property.1, rCt.down⟩, ?_⟩
  unfold nbeJudgment ExecutableChecking.judgment
  change (do
    let contextChecked ← nbeFormContext S.R choices (fun _ => none) f Γ
    let expected ← nbeSynth S.R choices (fun _ => none) f Γ E
    let level ← ExecutableChecking.asUniverse S.R (nbeWhnfReducer S.R (fun _ => none)) f expected.1
    let termChecked ← nbeCheck S.R choices (fun _ => none) f Γ t E
    pure (⟨contextChecked.down, level.val, expected.1, expected.2.down,
      level.property.2, level.property.1, termChecked.down⟩ :
      ExecutableChecking.JudgmentCertificate S.R Γ t E)) = _
  simp [hCtx', hSE', hUE', hCt', bind, Option.bind, pure]

/-- Simulation completeness of `nbeAcceptsEquality` on the bidirectional fragment. -/
theorem nbeAcceptsEquality_complete
    (headsTyped : ∀ {h u u' : Head}, S.R.headTyping h u → S.R.headTyping h u' → u = u')
    {choices : ExecutableChecking.HeadChoices S.R}
    (hChoices : HeadChoicesComplete S.R choices)
    {n : Nat} {Γ : Ctx Head n} {t u E : Tm Head n}
    (hΓ : BidirectionalCtx Γ) (hE : Bidirectional .synth E)
    (ht : Bidirectional .check t) (hu : Bidirectional .check u)
    (formed : CtxFormed S.R Γ) (tt : Typed S.R Γ t E) (tu : Typed S.R Γ u E)
    (eq : Equal S.R Γ t u E) :
    ∃ fuel,
      nbeAcceptsEquality S.R choices (fun _ => none) fuel Γ t u E = true := by
  obtain ⟨fCtx, rCtx, hCtx⟩ :=
    nbeFormContext_complete S facts roots heads algebra complete hComp hRoles
      headsTyped hChoices hΓ formed
  obtain ⟨uUniv, huUniv, tE⟩ := Typed.isType tt formed
  obtain ⟨TE, fSE, rE_exec, sE, hSE, hValE⟩ :=
    Bidirectional.executable_complete S facts roots heads algebra complete hComp hRoles
      headsTyped hChoices hE formed tE
  obtain ⟨u₀, rE, hu₀⟩ :=
    Synth.universe_whnf facts algebra headsTyped sE formed tE huUniv
  have rE' : RedTy S.R S.roles Γ rE_exec.1 (.head u₀) := hValE ▸ rE
  obtain ⟨fUE, nUE, hNUE, hValUE⟩ :=
    nbeWhnf_complete_of_whRed hComp hRoles rE'.red (head_whnf S.shape _)
  obtain ⟨uE, hUE, _⟩ :=
    asUniverse_of_whnf S.R (fun _ => none) hNUE hValUE hu₀
  obtain ⟨_, fCt, rCt, hCt⟩ :=
    Bidirectional.executable_complete S facts roots heads algebra complete hComp hRoles
      headsTyped hChoices ht formed tt
  obtain ⟨_, fCu, rCu, hCu⟩ :=
    Bidirectional.executable_complete S facts roots heads algebra complete hComp hRoles
      headsTyped hChoices hu formed tu
  have hAlg : Algorithmic S.R S.roles (.terms Γ t u E) :=
    complete formed eq
  obtain ⟨fCmp, rCmp, hCmp⟩ :=
    nbeCompare_complete_of_algorithmic (S := S) facts roots heads algebra hComp hRoles formed hAlg
  let f := Nat.max (Nat.max (Nat.max fCtx fSE) (Nat.max fUE fCt)) (Nat.max fCu fCmp)
  have hfCtx : fCtx ≤ f :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) (Nat.le_max_left _ _)
  have hfSE : fSE ≤ f :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) (Nat.le_max_left _ _)
  have hfUE : fUE ≤ f :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) (Nat.le_max_left _ _)
  have hfCt : fCt ≤ f :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) (Nat.le_max_left _ _)
  have hfCu : fCu ≤ f := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  have hfCmp : fCmp ≤ f := Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  have hCtx' := nbeFormContext_mono_eq S.R choices (fun _ => none) hfCtx hCtx
  have hSE' := nbeSynth_mono_eq S.R choices (fun _ => none) hfSE hSE
  have hUE' := asUniverse_mono_eq S.R (fun _ => none) hfUE hUE
  have hCt' := nbeCheck_mono_eq S.R choices (fun _ => none) hfCt hCt
  have hCu' := nbeCheck_mono_eq S.R choices (fun _ => none) hfCu hCu
  have hCmp' := nbeCompare_mono_eq S.R (fun _ => none) hfCmp hCmp
  have hJt : ExecutableChecking.judgment S.R choices (nbeWhnfReducer S.R (fun _ => none)) f Γ t E =
      some ⟨rCtx.down, uE.val, rE_exec.1, rE_exec.2.down, uE.property.2, uE.property.1, rCt.down⟩ := by
    unfold ExecutableChecking.judgment
    change (do
      let contextChecked ← nbeFormContext S.R choices (fun _ => none) f Γ
      let expected ← nbeSynth S.R choices (fun _ => none) f Γ E
      let level ← ExecutableChecking.asUniverse S.R (nbeWhnfReducer S.R (fun _ => none)) f expected.1
      let termChecked ← nbeCheck S.R choices (fun _ => none) f Γ t E
      pure (⟨contextChecked.down, level.val, expected.1, expected.2.down,
        level.property.2, level.property.1, termChecked.down⟩ :
        ExecutableChecking.JudgmentCertificate S.R Γ t E)) = _
    simp [hCtx', hSE', hUE', hCt', bind, Option.bind, pure]
  have hJu : ExecutableChecking.judgment S.R choices (nbeWhnfReducer S.R (fun _ => none)) f Γ u E =
      some ⟨rCtx.down, uE.val, rE_exec.1, rE_exec.2.down, uE.property.2, uE.property.1, rCu.down⟩ := by
    unfold ExecutableChecking.judgment
    change (do
      let contextChecked ← nbeFormContext S.R choices (fun _ => none) f Γ
      let expected ← nbeSynth S.R choices (fun _ => none) f Γ E
      let level ← ExecutableChecking.asUniverse S.R (nbeWhnfReducer S.R (fun _ => none)) f expected.1
      let termChecked ← nbeCheck S.R choices (fun _ => none) f Γ u E
      pure (⟨contextChecked.down, level.val, expected.1, expected.2.down,
        level.property.2, level.property.1, termChecked.down⟩ :
        ExecutableChecking.JudgmentCertificate S.R Γ u E)) = _
    simp [hCtx', hSE', hUE', hCu', bind, Option.bind, pure]
  refine ⟨f, ?_⟩
  unfold nbeAcceptsEquality ExecutableChecking.acceptsEquality ExecutableChecking.equality
  simp [hJt, hJu, hCmp', bind, Option.bind, pure]

end GenericNbECheckingCompleteness

/-! ### Concrete Instantiation for the Cumulative Universe Tower (`Tower`) -/

section TowerNbEChecking

open TowerModel

variable {L : Type} [LevelOrder L] [DecidableEq L]

instance : DecidableRel (LevelTower.rules L).headEq :=
  fun left right => LevelTower.instDecidableHeadEq left right

instance : DecidableRel (LevelTower.rules L).cumulative :=
  fun left right => LevelTower.instDecidableCumulative left right

instance (head : LevelTower.Head L) : Decidable ((LevelTower.rules L).isUniverse head) :=
  ExecutableTowerChoices.universeDecidable head

omit [DecidableEq L] in
private theorem levelTower_headsTyped {h u v : LevelTower.Head L}
    (first : (LevelTower.rules L).headTyping h u)
    (second : (LevelTower.rules L).headTyping h v) : u = v :=
  ((ExecutableTowerChoices.typing_exact h u).mp first).trans
    ((ExecutableTowerChoices.typing_exact h v).mp second).symm

/-- Bidirectional type synthesis in `LevelTower.rules L` powered by `nbeWhnfReducer`. -/
def levelTowerNbESynth (fuel : Nat) {n : Nat}
    (Γ : Ctx (LevelTower.Head L) n) (t : Tm (LevelTower.Head L) n) :
    Option (ExecutableChecking.SynthResult (LevelTower.rules L) Γ t) :=
  nbeSynth (LevelTower.rules L) ExecutableTowerChoices.choices (fun _ => none) fuel Γ t

/-- Bidirectional type checking in `LevelTower.rules L` powered by `nbeWhnfReducer`. -/
def levelTowerNbECheck (fuel : Nat) {n : Nat}
    (Γ : Ctx (LevelTower.Head L) n) (t A : Tm (LevelTower.Head L) n) :
    Option (ExecutableChecking.CheckResult (LevelTower.rules L) Γ t A) :=
  nbeCheck (LevelTower.rules L) ExecutableTowerChoices.choices (fun _ => none) fuel Γ t A

/-- Full judgment checking in `LevelTower.rules L` powered by `nbeWhnfReducer`. -/
def levelTowerNbEJudgment (fuel : Nat) {n : Nat}
    (Γ : Ctx (LevelTower.Head L) n) (t A : Tm (LevelTower.Head L) n) :
    Option (ExecutableChecking.JudgmentCertificate (LevelTower.rules L) Γ t A) :=
  nbeJudgment (LevelTower.rules L) ExecutableTowerChoices.choices (fun _ => none) fuel Γ t A

/-- Boolean judgment acceptance in `LevelTower.rules L` powered by `nbeWhnfReducer`. -/
def levelTowerNbEAccepts (fuel : Nat) {n : Nat}
    (Γ : Ctx (LevelTower.Head L) n) (t A : Tm (LevelTower.Head L) n) : Bool :=
  nbeAccepts (LevelTower.rules L) ExecutableTowerChoices.choices (fun _ => none) fuel Γ t A

/-- Qualified equality acceptance in `LevelTower.rules L` powered by `nbeWhnfReducer`. -/
def levelTowerNbEAcceptsEquality (fuel : Nat) {n : Nat}
    (Γ : Ctx (LevelTower.Head L) n) (t u A : Tm (LevelTower.Head L) n) : Bool :=
  nbeAcceptsEquality (LevelTower.rules L) ExecutableTowerChoices.choices (fun _ => none)
    fuel Γ t u A

/-- Specializations to `Tower` (`L = Nat`). -/
abbrev towerNbESynth (fuel : Nat) {n : Nat} (Γ : Tower.Ctx n) (t : Tower.Tm n) :=
  levelTowerNbESynth (L := Nat) fuel Γ t

abbrev towerNbECheck (fuel : Nat) {n : Nat} (Γ : Tower.Ctx n) (t A : Tower.Tm n) :=
  levelTowerNbECheck (L := Nat) fuel Γ t A

abbrev towerNbEJudgment (fuel : Nat) {n : Nat} (Γ : Tower.Ctx n) (t A : Tower.Tm n) :=
  levelTowerNbEJudgment (L := Nat) fuel Γ t A

abbrev towerNbEAccepts (fuel : Nat) {n : Nat} (Γ : Tower.Ctx n) (t A : Tower.Tm n) : Bool :=
  levelTowerNbEAccepts (L := Nat) fuel Γ t A

abbrev towerNbEAcceptsEquality (fuel : Nat) {n : Nat}
    (Γ : Tower.Ctx n) (t u A : Tower.Tm n) : Bool :=
  levelTowerNbEAcceptsEquality (L := Nat) fuel Γ t u A

/-- **Soundness of `levelTowerNbEAccepts`**:
Acceptance by the NbE-powered bidirectional checker implies declarative typing
`Typed (LevelTower.rules L) Γ t A` (and context formation `CtxFormed`). -/
theorem levelTowerNbEAccepts_sound (valuation : Nat → L)
    {fuel n : Nat} {Γ : Ctx (LevelTower.Head L) n} {t A : Tm (LevelTower.Head L) n}
    (hAcc : levelTowerNbEAccepts fuel Γ t A = true) :
    Typed (LevelTower.rules L) Γ t A := by
  let : DecidableRel (setting valuation).R.headEq :=
    fun left right => LevelTower.instDecidableHeadEq left right
  let : DecidableRel (setting valuation).R.cumulative :=
    fun left right => LevelTower.instDecidableCumulative left right
  let : ∀ head, Decidable ((setting valuation).R.isUniverse head) :=
    fun head => ExecutableTowerChoices.universeDecidable head
  exact ExecutableChecking.accepts_sound (S := setting valuation)
    facts roots heads algebra (fun {_ _} h => nomatch h)
    ExecutableTowerChoices.choices
    (nbeWhnfReducer (LevelTower.rules L) (fun _ => none)) hAcc

theorem towerNbEAccepts_sound
    {fuel n : Nat} {Γ : Tower.Ctx n} {t A : Tower.Tm n}
    (hAcc : towerNbEAccepts fuel Γ t A = true) :
    Typed Tower.rules Γ t A :=
  levelTowerNbEAccepts_sound (fun _ => 0) hAcc

/-- **Soundness of `levelTowerNbEAcceptsEquality`**:
Acceptance by the NbE-powered bidirectional equality checker implies declarative
typed equality `Equal (LevelTower.rules L) Γ t u A`. -/
theorem levelTowerNbEAcceptsEquality_sound (valuation : Nat → L)
    {fuel n : Nat} {Γ : Ctx (LevelTower.Head L) n} {t u A : Tm (LevelTower.Head L) n}
    (hAcc : levelTowerNbEAcceptsEquality fuel Γ t u A = true) :
    Equal (LevelTower.rules L) Γ t u A := by
  let : DecidableRel (setting valuation).R.headEq :=
    fun left right => LevelTower.instDecidableHeadEq left right
  let : DecidableRel (setting valuation).R.cumulative :=
    fun left right => LevelTower.instDecidableCumulative left right
  let : ∀ head, Decidable ((setting valuation).R.isUniverse head) :=
    fun head => ExecutableTowerChoices.universeDecidable head
  exact ExecutableChecking.acceptsEquality_sound (S := setting valuation)
    facts roots heads algebra (fun {_ _} h => nomatch h)
    ExecutableTowerChoices.choices
    (nbeWhnfReducer (LevelTower.rules L) (fun _ => none)) hAcc

theorem towerNbEAcceptsEquality_sound
    {fuel n : Nat} {Γ : Tower.Ctx n} {t u A : Tower.Tm n}
    (hAcc : towerNbEAcceptsEquality fuel Γ t u A = true) :
    Equal Tower.rules Γ t u A :=
  levelTowerNbEAcceptsEquality_sound (fun _ => 0) hAcc

omit [DecidableEq L] in
/-- The constructed head choices `ExecutableTowerChoices.choices` are complete
for `LevelTower.rules L`. -/
theorem levelTower_headChoices_complete :
    HeadChoicesComplete (LevelTower.rules L) ExecutableTowerChoices.choices where
  typing_complete := fun {_ _} _ => ⟨ExecutableTowerChoices.typing _, rfl⟩
  join_complete := by
    intro u v hu hv
    cases hu
    cases hv
    exact ⟨⟨.sort (.max _ _), .sorts _ _⟩, rfl⟩

/-- **Both-Directions Completeness & Soundness of `levelTowerNbECheck`**:
On the bidirectional checking fragment `Bidirectional .check t`, our executable
NbE checker `levelTowerNbECheck` succeeds at some finite `fuel` if and only if
`Typed (LevelTower.rules L) Γ t E` holds in a formed context `Γ` at a formed expected type `E`. -/
theorem levelTower_typed_iff_exists_fuel_nbeCheck (valuation : Nat → L)
    {n : Nat} {Γ : Ctx (LevelTower.Head L) n} {t E : Tm (LevelTower.Head L) n}
    (ht : Bidirectional .check t) (formed : CtxFormed (LevelTower.rules L) Γ)
    (expected : IsType (LevelTower.rules L) Γ E) :
    Typed (LevelTower.rules L) Γ t E ↔
      ∃ fuel, (levelTowerNbECheck fuel Γ t E).isSome := by
  constructor
  · intro typing
    let : DecidableRel (setting valuation).R.headEq :=
      fun left right => LevelTower.instDecidableHeadEq left right
    let : DecidableRel (setting valuation).R.cumulative :=
      fun left right => LevelTower.instDecidableCumulative left right
    let : ∀ head, Decidable ((setting valuation).R.isUniverse head) :=
      fun head => ExecutableTowerChoices.universeDecidable head
    obtain ⟨_, fuel, res, hCheck⟩ :=
      Bidirectional.executable_complete (setting valuation)
        facts roots heads algebra complete rfl rfl
        levelTower_headsTyped levelTower_headChoices_complete ht formed typing
    exact ⟨fuel, Option.isSome_iff_exists.mpr ⟨res, hCheck⟩⟩
  · rintro ⟨fuel, hSome⟩
    obtain ⟨res, hCheck⟩ := Option.isSome_iff_exists.mp hSome
    exact CheckingAlgorithm.sound (S := setting valuation)
      facts roots heads algebra (fun {_ _} h => nomatch h) res.down formed expected

theorem tower_typed_iff_exists_fuel_nbeCheck
    {n : Nat} {Γ : Tower.Ctx n} {t E : Tower.Tm n}
    (ht : Bidirectional .check t) (formed : CtxFormed Tower.rules Γ)
    (expected : IsType Tower.rules Γ E) :
    Typed Tower.rules Γ t E ↔
      ∃ fuel, (towerNbECheck fuel Γ t E).isSome :=
  levelTower_typed_iff_exists_fuel_nbeCheck (fun _ => 0) ht formed expected

/-- **Both-Directions Completeness & Soundness of `levelTowerNbESynth`**:
On the bidirectional synthesis fragment `Bidirectional .synth t`, our executable
NbE synthesizer `levelTowerNbESynth` succeeds at some finite `fuel` if and only if
`t` is typable (`∃ E, Typed (LevelTower.rules L) Γ t E`) in a formed context `Γ`. -/
theorem levelTower_typable_iff_exists_fuel_nbeSynth (valuation : Nat → L)
    {n : Nat} {Γ : Ctx (LevelTower.Head L) n} {t : Tm (LevelTower.Head L) n}
    (ht : Bidirectional .synth t) (formed : CtxFormed (LevelTower.rules L) Γ) :
    (∃ E, Typed (LevelTower.rules L) Γ t E) ↔
      ∃ fuel, (levelTowerNbESynth fuel Γ t).isSome := by
  constructor
  · rintro ⟨E, typing⟩
    let : DecidableRel (setting valuation).R.headEq :=
      fun left right => LevelTower.instDecidableHeadEq left right
    let : DecidableRel (setting valuation).R.cumulative :=
      fun left right => LevelTower.instDecidableCumulative left right
    let : ∀ head, Decidable ((setting valuation).R.isUniverse head) :=
      fun head => ExecutableTowerChoices.universeDecidable head
    obtain ⟨_, fuel, res, _, hSynth, _⟩ :=
      Bidirectional.executable_complete (setting valuation)
        facts roots heads algebra complete rfl rfl
        levelTower_headsTyped levelTower_headChoices_complete ht formed typing
    exact ⟨fuel, Option.isSome_iff_exists.mpr ⟨res, hSynth⟩⟩
  · rintro ⟨fuel, hSome⟩
    obtain ⟨res, hSynth⟩ := Option.isSome_iff_exists.mp hSome
    exact ⟨res.1, CheckingAlgorithm.sound (S := setting valuation)
      facts roots heads algebra (fun {_ _} h => nomatch h) res.2.down formed⟩

theorem tower_typable_iff_exists_fuel_nbeSynth
    {n : Nat} {Γ : Tower.Ctx n} {t : Tower.Tm n}
    (ht : Bidirectional .synth t) (formed : CtxFormed Tower.rules Γ) :
    (∃ E, Typed Tower.rules Γ t E) ↔
      ∃ fuel, (towerNbESynth fuel Γ t).isSome :=
  levelTower_typable_iff_exists_fuel_nbeSynth (fun _ => 0) ht formed

/-- **Both-Directions Completeness & Soundness of `levelTowerNbEAccepts`**:
On the bidirectional fragment (`BidirectionalCtx Γ`, `Bidirectional .synth E`,
`Bidirectional .check t`), `CtxFormed (LevelTower.rules L) Γ ∧ Typed (LevelTower.rules L) Γ t E`
holds if and only if there exists a finite `fuel` at which `levelTowerNbEAccepts` returns `true`. -/
theorem levelTower_typed_iff_exists_fuel_nbeAccepts (valuation : Nat → L)
    {n : Nat} {Γ : Ctx (LevelTower.Head L) n} {t E : Tm (LevelTower.Head L) n}
    (hΓ : BidirectionalCtx Γ) (hE : Bidirectional .synth E) (ht : Bidirectional .check t) :
    (CtxFormed (LevelTower.rules L) Γ ∧ Typed (LevelTower.rules L) Γ t E) ↔
      ∃ fuel, levelTowerNbEAccepts fuel Γ t E = true := by
  let : DecidableRel (setting valuation).R.headEq :=
    fun left right => LevelTower.instDecidableHeadEq left right
  let : DecidableRel (setting valuation).R.cumulative :=
    fun left right => LevelTower.instDecidableCumulative left right
  let : ∀ head, Decidable ((setting valuation).R.isUniverse head) :=
    fun head => ExecutableTowerChoices.universeDecidable head
  constructor
  · rintro ⟨formed, typing⟩
    obtain ⟨fuel, cert, hJ⟩ :=
      nbeJudgment_complete (setting valuation)
        facts roots heads algebra complete rfl rfl
        levelTower_headsTyped levelTower_headChoices_complete hΓ hE ht formed typing
    exact ⟨fuel, Option.isSome_iff_exists.mpr ⟨cert, hJ⟩⟩
  · rintro ⟨fuel, hAcc⟩
    obtain ⟨cert, hJ⟩ := Option.isSome_iff_exists.mp hAcc
    have formed : CtxFormed (LevelTower.rules L) Γ :=
      ExecutableChecking.ContextAlgorithm.sound (S := setting valuation)
        facts roots heads algebra (fun {_ _} h => nomatch h) cert.contextChecked
    exact ⟨formed, levelTowerNbEAccepts_sound valuation hAcc⟩

theorem tower_typed_iff_exists_fuel_nbeAccepts
    {n : Nat} {Γ : Tower.Ctx n} {t E : Tower.Tm n}
    (hΓ : BidirectionalCtx Γ) (hE : Bidirectional .synth E) (ht : Bidirectional .check t) :
    (CtxFormed Tower.rules Γ ∧ Typed Tower.rules Γ t E) ↔
      ∃ fuel, towerNbEAccepts fuel Γ t E = true :=
  levelTower_typed_iff_exists_fuel_nbeAccepts (fun _ => 0) hΓ hE ht

/-- **Both-Directions Completeness & Soundness of `levelTowerNbEAcceptsEquality`**:
On the bidirectional fragment (`BidirectionalCtx Γ`, `Bidirectional .synth E`,
`Bidirectional .check t`, `Bidirectional .check u`), qualified typed equality
holds if and only if there exists a finite `fuel` at which `levelTowerNbEAcceptsEquality`
returns `true`. -/
theorem levelTower_equal_iff_exists_fuel_nbeAcceptsEquality (valuation : Nat → L)
    {n : Nat} {Γ : Ctx (LevelTower.Head L) n} {t u E : Tm (LevelTower.Head L) n}
    (hΓ : BidirectionalCtx Γ) (hE : Bidirectional .synth E)
    (ht : Bidirectional .check t) (hu : Bidirectional .check u) :
    (CtxFormed (LevelTower.rules L) Γ ∧ Typed (LevelTower.rules L) Γ t E ∧
     Typed (LevelTower.rules L) Γ u E ∧ Equal (LevelTower.rules L) Γ t u E) ↔
      ∃ fuel, levelTowerNbEAcceptsEquality fuel Γ t u E = true := by
  let : DecidableRel (setting valuation).R.headEq :=
    fun left right => LevelTower.instDecidableHeadEq left right
  let : DecidableRel (setting valuation).R.cumulative :=
    fun left right => LevelTower.instDecidableCumulative left right
  let : ∀ head, Decidable ((setting valuation).R.isUniverse head) :=
    fun head => ExecutableTowerChoices.universeDecidable head
  constructor
  · rintro ⟨formed, tt, tu, eq⟩
    exact nbeAcceptsEquality_complete (setting valuation)
      facts roots heads algebra complete rfl rfl
      levelTower_headsTyped levelTower_headChoices_complete hΓ hE ht hu formed tt tu eq
  · rintro ⟨fuel, hAcc⟩
    obtain ⟨cert, hEq⟩ := Option.isSome_iff_exists.mp hAcc
    have hJt : levelTowerNbEAccepts fuel Γ t E = true := by
      unfold ExecutableChecking.equality at hEq
      cases h1 : ExecutableChecking.judgment (LevelTower.rules L) ExecutableTowerChoices.choices
          (nbeWhnfReducer (LevelTower.rules L) (fun _ => none)) fuel Γ t E with
      | none => simp [h1, bind, Option.bind] at hEq
      | some c1 => exact Option.isSome_iff_exists.mpr ⟨c1, h1⟩
    have hJu : levelTowerNbEAccepts fuel Γ u E = true := by
      unfold ExecutableChecking.equality at hEq
      cases h1 : ExecutableChecking.judgment (LevelTower.rules L) ExecutableTowerChoices.choices
          (nbeWhnfReducer (LevelTower.rules L) (fun _ => none)) fuel Γ t E with
      | none => simp [h1, bind, Option.bind] at hEq
      | some c1 =>
          cases h2 : ExecutableChecking.judgment (LevelTower.rules L) ExecutableTowerChoices.choices
              (nbeWhnfReducer (LevelTower.rules L) (fun _ => none)) fuel Γ u E with
          | none => simp [h1, h2, bind, Option.bind] at hEq
          | some c2 => exact Option.isSome_iff_exists.mpr ⟨c2, h2⟩
    have formed : CtxFormed (LevelTower.rules L) Γ :=
      ExecutableChecking.ContextAlgorithm.sound (S := setting valuation)
        facts roots heads algebra (fun {_ _} h => nomatch h) cert.firstChecked.contextChecked
    exact ⟨formed,
      levelTowerNbEAccepts_sound valuation hJt,
      levelTowerNbEAccepts_sound valuation hJu,
      levelTowerNbEAcceptsEquality_sound valuation hAcc⟩

theorem tower_equal_iff_exists_fuel_nbeAcceptsEquality
    {n : Nat} {Γ : Tower.Ctx n} {t u E : Tower.Tm n}
    (hΓ : BidirectionalCtx Γ) (hE : Bidirectional .synth E)
    (ht : Bidirectional .check t) (hu : Bidirectional .check u) :
    (CtxFormed Tower.rules Γ ∧ Typed Tower.rules Γ t E ∧
     Typed Tower.rules Γ u E ∧ Equal Tower.rules Γ t u E) ↔
      ∃ fuel, towerNbEAcceptsEquality fuel Γ t u E = true :=
  levelTower_equal_iff_exists_fuel_nbeAcceptsEquality (fun _ => 0) hΓ hE ht hu

omit [DecidableEq L] in
/-- Specialization of the existing bidirectional kernel equivalence `Check.iff_typed`
(from `Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Checking`)
to `LevelTower.rules L`. For the executable NbE checker biconditional, see
`levelTower_typed_iff_exists_fuel_nbeCheck` and `levelTower_typed_iff_exists_fuel_nbeAccepts`. -/
theorem tower_check_iff_typed (valuation : Nat → L)
    {n : Nat} {Γ : Ctx (LevelTower.Head L) n} {t E : Tm (LevelTower.Head L) n}
    (fragment : Bidirectional .check t) (formed : CtxFormed (LevelTower.rules L) Γ) :
    Check (LevelTower.rules L) (fun _ => .rigid) Γ t E ↔
      Typed (LevelTower.rules L) Γ t E :=
  Check.iff_typed (S := setting valuation) facts algebra levelTower_headsTyped fragment formed

omit [DecidableEq L] in
/-- Specialization of the existing bidirectional kernel synthesis equivalence
`Synth.exists_iff_typable` (from `Checking.lean`) to `LevelTower.rules L`.
For the executable NbE synthesizer biconditional, see
`levelTower_typable_iff_exists_fuel_nbeSynth`. -/
theorem tower_synth_exists_iff_typable (valuation : Nat → L)
    {n : Nat} {Γ : Ctx (LevelTower.Head L) n} {t : Tm (LevelTower.Head L) n}
    (fragment : Bidirectional .synth t) (formed : CtxFormed (LevelTower.rules L) Γ) :
    (∃ T, Synth (LevelTower.rules L) (fun _ => .rigid) Γ t T) ↔
      ∃ E, Typed (LevelTower.rules L) Γ t E :=
  Synth.exists_iff_typable (S := setting valuation) facts algebra levelTower_headsTyped fragment formed

omit [DecidableEq L] in
/-- Specialization of the existing bidirectional kernel type-formation equivalence
`Synth.isType_iff` (from `Checking.lean`) to `LevelTower.rules L`. -/
theorem tower_synth_isType_iff (valuation : Nat → L)
    {n : Nat} {Γ : Ctx (LevelTower.Head L) n} {A : Tm (LevelTower.Head L) n}
    (fragment : Bidirectional .synth A) (formed : CtxFormed (LevelTower.rules L) Γ) :
    (∃ T u, Synth (LevelTower.rules L) (fun _ => .rigid) Γ A T ∧
      RedTy (LevelTower.rules L) (fun _ => .rigid) Γ T (.head u) ∧
      (LevelTower.rules L).isUniverse u) ↔
    IsType (LevelTower.rules L) Γ A :=
  (Synth.isType_iff (S := setting valuation) facts algebra levelTower_headsTyped fragment formed).symm

end TowerNbEChecking

/-! ### Concrete Instantiation for the Computing Natural-Number Calculus (`TowerNumbersModel`) -/

section TowerNumbersNbEChecking

open TowerNumbersModel

variable (level : LevelExpr Nat)

/-- Boolean judgment acceptance in `TowerNumbersModel.rules level` powered by
the closure-based NbE weak-head reducer `nbeWhnfReducer`. -/
def towerNumbersNbEAccepts (fuel : Nat) {n : Nat}
    (Γ : Ctx Tower.Head n) (t A : Tm Tower.Head n) : Bool :=
  nbeAccepts (TowerNumbersModel.rules level)
    (ExecutableTowerNumbers.choices level)
    (ExecutableTowerNumbers.root level)
    fuel Γ t A

/-- Qualified equality acceptance in `TowerNumbersModel.rules level` powered by
the closure-based NbE weak-head reducer `nbeWhnfReducer`. -/
def towerNumbersNbEAcceptsEquality (fuel : Nat) {n : Nat}
    (Γ : Ctx Tower.Head n) (t u A : Tm Tower.Head n) : Bool :=
  nbeAcceptsEquality (TowerNumbersModel.rules level)
    (ExecutableTowerNumbers.choices level)
    (ExecutableTowerNumbers.root level)
    fuel Γ t u A

/-- **Soundness of `towerNumbersNbEAccepts`**:
Acceptance by the NbE-powered bidirectional checker implies declarative typing
`Typed (TowerNumbersModel.rules level) Γ t A`. -/
theorem towerNumbersNbEAccepts_sound
    {fuel n : Nat} {Γ : Ctx Tower.Head n} {t A : Tm Tower.Head n}
    (hAcc : towerNumbersNbEAccepts level fuel Γ t A = true) :
    Typed (TowerNumbersModel.rules level) Γ t A := by
  let : DecidableRel (setting level (fun _ => 0)).R.headEq :=
    fun first second => LevelTower.instDecidableHeadEq first second
  let : DecidableRel (setting level (fun _ => 0)).R.cumulative :=
    fun first second => LevelTower.instDecidableCumulative first second
  let : ∀ head, Decidable ((setting level (fun _ => 0)).R.isUniverse head) :=
    fun head => ExecutableTowerChoices.universeDecidable head
  exact ExecutableChecking.accepts_sound (S := setting level (fun _ => 0))
    (facts level) (roots level) (heads level) (algebra level)
    (ExecutableTowerNumbers.declaredTypesFormed level)
    (ExecutableTowerNumbers.choices level)
    (nbeWhnfReducer (TowerNumbersModel.rules level) (ExecutableTowerNumbers.root level))
    hAcc

/-- **Soundness of `towerNumbersNbEAcceptsEquality`**:
Acceptance by the NbE-powered equality checker implies declarative typed equality
`Equal (TowerNumbersModel.rules level) Γ t u A`. -/
theorem towerNumbersNbEAcceptsEquality_sound
    {fuel n : Nat} {Γ : Ctx Tower.Head n} {t u A : Tm Tower.Head n}
    (hAcc : towerNumbersNbEAcceptsEquality level fuel Γ t u A = true) :
    Equal (TowerNumbersModel.rules level) Γ t u A := by
  let : DecidableRel (setting level (fun _ => 0)).R.headEq :=
    fun first second => LevelTower.instDecidableHeadEq first second
  let : DecidableRel (setting level (fun _ => 0)).R.cumulative :=
    fun first second => LevelTower.instDecidableCumulative first second
  let : ∀ head, Decidable ((setting level (fun _ => 0)).R.isUniverse head) :=
    fun head => ExecutableTowerChoices.universeDecidable head
  exact ExecutableChecking.acceptsEquality_sound (S := setting level (fun _ => 0))
    (facts level) (roots level) (heads level) (algebra level)
    (ExecutableTowerNumbers.declaredTypesFormed level)
    (ExecutableTowerNumbers.choices level)
    (nbeWhnfReducer (TowerNumbersModel.rules level) (ExecutableTowerNumbers.root level))
    hAcc

end TowerNumbersNbEChecking

/-! ## Finite replay with typed conversion obligations -/

section NIKStageALink

open FormationSensitiveRuleSignature
open FormationSensitiveChecking
open Mettapedia.GSLT.LanguageDef.BootstrapCell
open Mettapedia.GSLT.LanguageDef.KernelAuthority

variable {Head : Type} (R : Rules Head) [DecidableEq Head]
variable [DecidableRel R.headTyping] [DecidablePred R.isUniverse]
variable [∀ u v w, Decidable (R.join u v w)] [DecidableRel R.cumulative]
variable (root : ExecutableReduction.RootEvaluator R)
variable (headEqB : Head → Head → Bool)
variable (hHeadEq : ∀ h₁ h₂, headEqB h₁ h₂ = true → h₁ = h₂ ∨ R.headEq h₁ h₂)

/-- **Typed Conversion Obligation (`TypedConvObligation`)**:
Every `.conv` node in a `FormationSensitive.Typing R Γ t B` derivation inside a
formed context `FormationSensitive.ContextFormation R Γ` (under `UniverseRegularity R`)
satisfies `TypedConvObligation R Γ A B`:
1. the ambient context `Γ` is formed (`FormationSensitive.ContextFormation R Γ`);
2. the source type `A` is formed in some universe `uA` (`FormationSensitive.Typing R Γ A (.head uA)`);
3. the target type `B` is formed in some universe `uB` (`FormationSensitive.Typing R Γ B (.head uB)`);
4. `Conv R.headEq A B R.computation` holds.

Unlike raw untyped `Conv` (which holds by reflexivity on diverging untyped terms
such as `Ω = (λ x. x x) (λ x. x x)`), `TypedConvObligation` quantifies strictly
over well-formed types in formed contexts. -/
structure TypedConvObligation {Head : Type} (R : Rules Head) {n : Nat}
    (Γ : Ctx Head n) (A B : Tm Head n) : Prop where
  context : FormationSensitive.ContextFormation R Γ
  sourceFormed : ∃ uA, R.isUniverse uA ∧ FormationSensitive.Typing R Γ A (.head uA)
  targetFormed : ∃ uB, R.isUniverse uB ∧ FormationSensitive.Typing R Γ B (.head uB)
  converted : Conv R.headEq A B R.computation

/-- **Typed Conversion Completeness (`TypedConvComplete`)**:
Completeness of closure-based NbE normal-form conversion restricted strictly to
well-typed conversion obligations `TypedConvObligation R Γ A B`. -/
def TypedConvComplete {Head : Type} (R : Rules Head)
    (root : ExecutableReduction.RootEvaluator R)
    (headEqB : Head → Head → Bool) : Prop :=
  ∀ {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n},
    TypedConvObligation R Γ A B →
      ∃ fuel : Nat, nbeConvNf R root headEqB fuel A B = true

/-- `LevelTower.rules L` satisfies `FormationSensitive.UniverseRegularity` unconditionally. -/
theorem levelTower_universeRegularity {L : Type} [LevelOrder L] :
    FormationSensitive.UniverseRegularity (LevelTower.rules L) where
  head_target := by
    intro h u ht
    cases ht with
    | legacyGround => exact .sort _
    | sort l => exact .sort _
  join_target := by
    intro u v w hj
    cases hj with
    | sorts u v => exact .sort _
  cumulative_target := by
    intro u v hc
    cases u with
    | legacyGround => cases hc
    | sort left =>
        cases v with
        | legacyGround => cases hc
        | sort right => exact .sort _
  universe_typed := by
    intro u hu
    cases hu with
    | sort l => exact ⟨.sort (.succ l), .sort l, .sort (.succ l)⟩

theorem tower_universeRegularity :
    FormationSensitive.UniverseRegularity Tower.rules :=
  levelTower_universeRegularity (L := Nat)

/-- In `StructuralTypingReplay`, replacing step-by-step `StructuralConversionCode`
trees with a fuel bound `Nat` for verified NbE conversion (`nbeConvNf`). -/
abbrev NbEConversionFuel (_n : Nat) : Type := Nat

/-- Structural typing replay certificate whose `.convert` nodes carry only a `Nat`
fuel bound for `nbeConvNf` instead of a step-by-step `StructuralConversionCode` tree. -/
abbrev CodeWithNbE (Head : Type) (n : Nat) : Type :=
  StructuralTypingReplay.Code Head NbEConversionFuel n

/-- Context formation certificate using `NbEConversionFuel`. -/
abbrev ContextCodeWithNbE (Head : Type) (n : Nat) : Type :=
  StructuralTypingReplay.ContextCode Head NbEConversionFuel n

/-- The NbE conversion check plugged into `StructuralTypingReplay.check`:
runs `nbeConvNf` with the supplied fuel bound. -/
def nbeConversionCheck {n : Nat} (fuel : NbEConversionFuel n)
    (left right : Tm Head n) : Bool :=
  nbeConvNf R root headEqB fuel left right

omit [DecidableEq Head] [DecidableRel R.headTyping] [DecidablePred R.isUniverse] [∀ u v w, Decidable (R.join u v w)] [DecidableRel R.cumulative] in
include hHeadEq in
theorem nbeConversionCheck_sound {n : Nat} {fuel : NbEConversionFuel n}
    {left right : Tm Head n}
    (h : nbeConversionCheck R root headEqB fuel left right = true) :
    Conv R.headEq left right R.computation :=
  nbeConvNf_sound R root hHeadEq h

/-- Replay a typing certificate using verified NbE conversion (`nbeConvNf`) at
every `.convert` node instead of step-by-step conversion path replay. -/
def checkReplayWithNbE {n : Nat} (Γ : Ctx Head n) (subject type : Tm Head n)
    (code : CodeWithNbE Head n) : Bool :=
  StructuralTypingReplay.check R (nbeConversionCheck R root headEqB) Γ subject type code

/-- Replay a context formation certificate using verified NbE conversion. -/
def checkContextWithNbE {n : Nat} (Γ : Ctx Head n)
    (code : ContextCodeWithNbE Head n) : Bool :=
  StructuralTypingReplay.checkContext R (nbeConversionCheck R root headEqB) Γ code

/-- Replay a full judgment (context + typing) using verified NbE conversion. -/
def checkJudgmentWithNbE {n : Nat} (Γ : Ctx Head n) (subject type : Tm Head n)
    (contextCode : ContextCodeWithNbE Head n) (termCode : CodeWithNbE Head n) : Bool :=
  StructuralTypingReplay.checkJudgment R (nbeConversionCheck R root headEqB)
    Γ subject type contextCode termCode

include hHeadEq in
/-- **Soundness of `checkReplayWithNbE`**:
Every certificate accepted by `checkReplayWithNbE` yields a genuine
`FormationSensitive.Typing R Γ subject type` derivation. -/
theorem checkReplayWithNbE_sound {n : Nat} {Γ : Ctx Head n} {subject type : Tm Head n}
    {code : CodeWithNbE Head n}
    (h : checkReplayWithNbE R root headEqB Γ subject type code = true) :
    FormationSensitive.Typing R Γ subject type :=
  StructuralTypingReplay.check_sound R (nbeConversionCheck R root headEqB)
    (fun checked => nbeConversionCheck_sound R root headEqB hHeadEq checked) code h

include hHeadEq in
theorem checkContextWithNbE_sound {n : Nat} {Γ : Ctx Head n}
    {code : ContextCodeWithNbE Head n}
    (h : checkContextWithNbE R root headEqB Γ code = true) :
    FormationSensitive.ContextFormation R Γ :=
  StructuralTypingReplay.checkContext_sound R (nbeConversionCheck R root headEqB)
    (fun checked => nbeConversionCheck_sound R root headEqB hHeadEq checked) code h

include hHeadEq in
theorem checkJudgmentWithNbE_sound {n : Nat} {Γ : Ctx Head n} {subject type : Tm Head n}
    {contextCode : ContextCodeWithNbE Head n} {termCode : CodeWithNbE Head n}
    (h : checkJudgmentWithNbE R root headEqB Γ subject type contextCode termCode = true) :
    FormationSensitive.Judgment R Γ subject type :=
  StructuralTypingReplay.checkJudgment_sound R (nbeConversionCheck R root headEqB)
    (fun checked => nbeConversionCheck_sound R root headEqB hHeadEq checked) h

/-- **Completeness of `checkReplayWithNbE` under `TypedConvComplete`**:
Because every `.conv` node in a `FormationSensitive.Typing` derivation inside a
formed context `Γ` (under `UniverseRegularity R`) satisfies `TypedConvObligation R Γ A B`
by `FormationSensitive.Typing.regularity`, completeness of `checkReplayWithNbE`
requires `TypedConvComplete` ONLY on well-typed conversion obligations, never on
raw untyped terms. -/
theorem checkReplayWithNbE_complete_of_typed
    (universes : FormationSensitive.UniverseRegularity R)
    (hComplete : TypedConvComplete R root headEqB)
    {n : Nat} {Γ : Ctx Head n} {subject type : Tm Head n}
    (typing : FormationSensitive.Typing R Γ subject type)
    (formed : FormationSensitive.ContextFormation R Γ) :
    ∃ code : CodeWithNbE Head n,
      checkReplayWithNbE R root headEqB Γ subject type code = true := by
  induction typing with
  | headType typed =>
      exact ⟨.headType, by simp [checkReplayWithNbE, StructuralTypingReplay.check, typed]⟩
  | var _ =>
      exact ⟨.var, by simp [checkReplayWithNbE, StructuralTypingReplay.check]⟩
  | @const n context name declared u known _ isUniverse ih =>
      obtain ⟨formation, accepted⟩ := ih .nil
      exact ⟨.const u formation, by
        simp [checkReplayWithNbE, StructuralTypingReplay.check, known, isUniverse] at accepted ⊢
        exact accepted⟩
  | @piForm n context A B u v w tA isU _ isV joined ihA ihB =>
      obtain ⟨domain, domainAccepted⟩ := ihA formed
      obtain ⟨body, bodyAccepted⟩ := ihB (.snoc formed tA isU)
      exact ⟨.piForm u v domain body, by
        simp [checkReplayWithNbE, StructuralTypingReplay.check, isU, isV, joined] at domainAccepted bodyAccepted ⊢
        exact ⟨domainAccepted, bodyAccepted⟩⟩
  | @sigmaForm n context A B u v w tA isU _ isV joined ihA ihB =>
      obtain ⟨domain, domainAccepted⟩ := ihA formed
      obtain ⟨body, bodyAccepted⟩ := ihB (.snoc formed tA isU)
      exact ⟨.sigmaForm u v domain body, by
        simp [checkReplayWithNbE, StructuralTypingReplay.check, isU, isV, joined] at domainAccepted bodyAccepted ⊢
        exact ⟨domainAccepted, bodyAccepted⟩⟩
  | @lamIntro n context A body B u tPi isUniverse _ ihFormation ihBody =>
      obtain ⟨formation, formationAccepted⟩ := ihFormation formed
      obtain ⟨uA, _, _, tA, isUA, _, _, _⟩ := tPi.piFormation
      obtain ⟨bodyCode, bodyAccepted⟩ := ihBody (.snoc formed tA isUA)
      exact ⟨.lamIntro u formation bodyCode, by
        simp [checkReplayWithNbE, StructuralTypingReplay.check, isUniverse] at formationAccepted bodyAccepted ⊢
        exact ⟨formationAccepted, bodyAccepted⟩⟩
  | @appElim n context function argument A B _ _ ihFunction ihArgument =>
      obtain ⟨functionCode, functionAccepted⟩ := ihFunction formed
      obtain ⟨argumentCode, argumentAccepted⟩ := ihArgument formed
      exact ⟨.appElim A B functionCode argumentCode, by
        simp [checkReplayWithNbE, StructuralTypingReplay.check] at functionAccepted argumentAccepted ⊢
        exact ⟨functionAccepted, argumentAccepted⟩⟩
  | @pairIntro n context a b A B u _ isUniverse _ _ ihFormation ihFirst ihSecond =>
      obtain ⟨formation, formationAccepted⟩ := ihFormation formed
      obtain ⟨first, firstAccepted⟩ := ihFirst formed
      obtain ⟨second, secondAccepted⟩ := ihSecond formed
      exact ⟨.pairIntro u formation first second, by
        simp [checkReplayWithNbE, StructuralTypingReplay.check, isUniverse] at formationAccepted firstAccepted secondAccepted ⊢
        exact ⟨⟨formationAccepted, firstAccepted⟩, secondAccepted⟩⟩
  | @fstElim n context pair A B _ ih =>
      obtain ⟨code, accepted⟩ := ih formed
      exact ⟨.fstElim B code, by
        simp [checkReplayWithNbE, StructuralTypingReplay.check] at accepted ⊢
        exact accepted⟩
  | @sndElim n context pair A B _ ih =>
      obtain ⟨code, accepted⟩ := ih formed
      exact ⟨.sndElim A B code, by
        simp [checkReplayWithNbE, StructuralTypingReplay.check] at accepted ⊢
        exact accepted⟩
  | @idForm n context A a b u _ isUniverse _ _ ihFormation ihLeft ihRight =>
      obtain ⟨formation, formationAccepted⟩ := ihFormation formed
      obtain ⟨left, leftAccepted⟩ := ihLeft formed
      obtain ⟨right, rightAccepted⟩ := ihRight formed
      exact ⟨.idForm u formation left right, by
        simp [checkReplayWithNbE, StructuralTypingReplay.check, isUniverse] at formationAccepted leftAccepted rightAccepted ⊢
        exact ⟨⟨formationAccepted, leftAccepted⟩, rightAccepted⟩⟩
  | @reflIntro n context a A _ ih =>
      obtain ⟨code, accepted⟩ := ih formed
      exact ⟨.reflIntro A code, by
        simp [checkReplayWithNbE, StructuralTypingReplay.check] at accepted ⊢
        exact accepted⟩
  | @cumul n context term u v _ order ih =>
      obtain ⟨code, accepted⟩ := ih formed
      exact ⟨.cumul u code, by
        simp [checkReplayWithNbE, StructuralTypingReplay.check, order] at accepted ⊢
        exact accepted⟩
  | @conv n context term A B u tTerm tB isUniverse converted ihSource ihFormation =>
      obtain ⟨source, sourceAccepted⟩ := ihSource formed
      obtain ⟨formation, formationAccepted⟩ := ihFormation formed
      obtain ⟨uA, isUA, tA⟩ := tTerm.regularity universes formed
      have ob : TypedConvObligation R context A B :=
        ⟨formed, ⟨uA, isUA, tA⟩, ⟨u, isUniverse, tB⟩, converted⟩
      obtain ⟨conversion, conversionAccepted⟩ := hComplete ob
      exact ⟨.convert A u source formation conversion, by
        simp [checkReplayWithNbE, StructuralTypingReplay.check, nbeConversionCheck,
          isUniverse, conversionAccepted] at sourceAccepted formationAccepted ⊢
        exact ⟨sourceAccepted, formationAccepted⟩⟩

/-- **Completeness of `checkContextWithNbE` under `TypedConvComplete`**: -/
theorem checkContextWithNbE_complete_of_typed
    (universes : FormationSensitive.UniverseRegularity R)
    (hComplete : TypedConvComplete R root headEqB)
    {n : Nat} {Γ : Ctx Head n}
    (formed : FormationSensitive.ContextFormation R Γ) :
    ∃ code : ContextCodeWithNbE Head n,
      checkContextWithNbE R root headEqB Γ code = true := by
  induction formed with
  | nil => exact ⟨.nil, rfl⟩
  | @snoc n context type u priorFormed typeFormed isUniverse ih =>
      obtain ⟨prior, priorAccepted⟩ := ih
      obtain ⟨formation, formationAccepted⟩ :=
        checkReplayWithNbE_complete_of_typed R root headEqB universes hComplete typeFormed priorFormed
      exact ⟨.snoc prior u formation, by
        simp [checkContextWithNbE, StructuralTypingReplay.checkContext, checkReplayWithNbE,
          isUniverse] at priorAccepted formationAccepted ⊢
        exact ⟨priorAccepted, formationAccepted⟩⟩

include hHeadEq in
/-- **Both-Directions Judgment Equivalence (`judgment_iff_checkedReplayWithNbE`)**:
Under `UniverseRegularity R` and `TypedConvComplete R root headEqB` (restricted to
`TypedConvObligation`), `FormationSensitive.Judgment R Γ subject type` holds if and
only if there exist `contextCode` and `termCode` accepted by `checkJudgmentWithNbE`. -/
theorem judgment_iff_checkedReplayWithNbE
    (universes : FormationSensitive.UniverseRegularity R)
    (hComplete : TypedConvComplete R root headEqB)
    {n : Nat} {Γ : Ctx Head n} {subject type : Tm Head n} :
    FormationSensitive.Judgment R Γ subject type ↔
      ∃ (contextCode : ContextCodeWithNbE Head n) (termCode : CodeWithNbE Head n),
        checkJudgmentWithNbE R root headEqB Γ subject type contextCode termCode = true := by
  constructor
  · intro j
    obtain ⟨cCode, hc⟩ := checkContextWithNbE_complete_of_typed R root headEqB universes hComplete j.context
    obtain ⟨tCode, ht⟩ := checkReplayWithNbE_complete_of_typed R root headEqB universes hComplete j.typing j.context
    exact ⟨cCode, tCode, by
      simp [checkJudgmentWithNbE, StructuralTypingReplay.checkJudgment,
        checkContextWithNbE, checkReplayWithNbE] at hc ht ⊢
      exact ⟨hc, ht⟩⟩
  · rintro ⟨cCode, tCode, h⟩
    exact checkJudgmentWithNbE_sound R root headEqB hHeadEq h

include hHeadEq in
/-- Mint a `DerivationGraph.CheckedJudgment (FormationSensitiveChecking.rules R)`
directly from a `CodeWithNbE` certificate accepted by `checkReplayWithNbE`. -/
def mintReplayWithNbE (j : Judgment Head) (code : CodeWithNbE Head j.arity) :
    Option (DerivationGraph.CheckedJudgment (FormationSensitiveChecking.rules R)) :=
  if accepted : checkReplayWithNbE R root headEqB j.context j.subject j.type code = true then
    some (DerivationGraph.CheckedJudgment.ofDerivation j
      ((FormationSensitiveChecking.typing_iff_derives j).mp
        (checkReplayWithNbE_sound R root headEqB hHeadEq accepted)))
  else none

include hHeadEq in
theorem mintReplayWithNbE_iff (j : Judgment Head) (code : CodeWithNbE Head j.arity) :
    (mintReplayWithNbE R root headEqB hHeadEq j code).map
      DerivationGraph.CheckedJudgment.judgment = some j ↔
      checkReplayWithNbE R root headEqB j.context j.subject j.type code = true := by
  unfold mintReplayWithNbE
  split <;> simp_all [DerivationGraph.CheckedJudgment.ofDerivation]

/-- Local rule code for `FormationSensitiveChecking` where `.convert` carries only
a `Nat` fuel bound for `nbeConvNf` instead of a `StructuralConversionCode` tree. -/
inductive FSCodeWithNbE (Head : Type) : Judgment Head → Type where
  | headType {n : Nat} {Γ : Ctx Head n} {h u : Head} :
      FSCodeWithNbE Head (judgment Γ (.head h) (.head u))
  | var {n : Nat} {Γ : Ctx Head n} (i : Fin n) :
      FSCodeWithNbE Head (judgment Γ (.var i) (Ctx.lookup Γ i))
  | const {n : Nat} {Γ : Ctx Head n} {name : DeclName} {type : Tm Head 0} {u : Head} :
      FSCodeWithNbE Head (judgment Γ (.const name) (liftClosed type))
  | piForm {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {B : Tm Head (n + 1)}
      {u v w : Head} : FSCodeWithNbE Head (judgment Γ (.pi A B) (.head w))
  | sigmaForm {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {B : Tm Head (n + 1)}
      {u v w : Head} : FSCodeWithNbE Head (judgment Γ (.sigma A B) (.head w))
  | lamIntro {n : Nat} {Γ : Ctx Head n} {A : Tm Head n}
      {body B : Tm Head (n + 1)} {u : Head} :
      FSCodeWithNbE Head (judgment Γ (.lam body) (.pi A B))
  | appElim {n : Nat} {Γ : Ctx Head n} {g a A : Tm Head n} {B : Tm Head (n + 1)} :
      FSCodeWithNbE Head (judgment Γ (.app g a) (inst0 a B))
  | pairIntro {n : Nat} {Γ : Ctx Head n} {a b A : Tm Head n}
      {B : Tm Head (n + 1)} {u : Head} :
      FSCodeWithNbE Head (judgment Γ (.pair a b) (.sigma A B))
  | fstElim {n : Nat} {Γ : Ctx Head n} {p A : Tm Head n} {B : Tm Head (n + 1)} :
      FSCodeWithNbE Head (judgment Γ (.fst p) A)
  | sndElim {n : Nat} {Γ : Ctx Head n} {p A : Tm Head n} {B : Tm Head (n + 1)} :
      FSCodeWithNbE Head (judgment Γ (.snd p) (inst0 (.fst p) B))
  | idForm {n : Nat} {Γ : Ctx Head n} {A a b : Tm Head n} {u : Head} :
      FSCodeWithNbE Head (judgment Γ (.id A a b) (.head u))
  | reflIntro {n : Nat} {Γ : Ctx Head n} {a A : Tm Head n} :
      FSCodeWithNbE Head (judgment Γ (.refl a) (.id A a a))
  | cumul {n : Nat} {Γ : Ctx Head n} {t : Tm Head n} {u v : Head} :
      FSCodeWithNbE Head (judgment Γ t (.head v))
  | convert {n : Nat} {Γ : Ctx Head n} {t A B : Tm Head n} {u : Head}
      (fuel : Nat) :
      FSCodeWithNbE Head (judgment Γ t B)

include hHeadEq in
/-- Decode an `FSCodeWithNbE` into a `FormationSensitiveRuleSignature.Rule R j`
by running `nbeConvNf` at `.convert` nodes and applying `nbeConvNf_sound`. -/
def decodeWithNbE {j : Judgment Head} : FSCodeWithNbE Head j → Option (Rule R j)
  | @FSCodeWithNbE.headType _ _ Γ h u =>
      if typed : R.headTyping h u then some (.headType typed) else none
  | .var i => some (.var i)
  | @FSCodeWithNbE.const _ _ Γ name type u =>
      if h : R.constantType name = some type then
        if hu : R.isUniverse u then some (.const h hu) else none
      else none
  | @FSCodeWithNbE.piForm _ _ Γ A B u v w =>
      if hu : R.isUniverse u then
        if hv : R.isUniverse v then
          if hw : R.join u v w then some (.piForm hu hv hw) else none
        else none
      else none
  | @FSCodeWithNbE.sigmaForm _ _ Γ A B u v w =>
      if hu : R.isUniverse u then
        if hv : R.isUniverse v then
          if hw : R.join u v w then some (.sigmaForm hu hv hw) else none
        else none
      else none
  | @FSCodeWithNbE.lamIntro _ _ Γ A body B u =>
      if hu : R.isUniverse u then some (.lamIntro hu) else none
  | @FSCodeWithNbE.appElim _ _ Γ g a A B =>
      some (.appElim (A := A) (B := B))
  | @FSCodeWithNbE.pairIntro _ _ Γ a b A B u =>
      if hu : R.isUniverse u then some (.pairIntro hu) else none
  | @FSCodeWithNbE.fstElim _ _ Γ p A B =>
      some (.fstElim (B := B))
  | @FSCodeWithNbE.sndElim _ _ Γ p A B =>
      some (.sndElim (A := A) (B := B))
  | @FSCodeWithNbE.idForm _ _ Γ A a b u =>
      if hu : R.isUniverse u then some (.idForm hu) else none
  | .reflIntro => some .reflIntro
  | @FSCodeWithNbE.cumul _ _ Γ t u v =>
      if h : R.cumulative u v then some (.cumul h) else none
  | @FSCodeWithNbE.convert _ _ Γ t A B u fuel =>
      if hu : R.isUniverse u then
        if h : nbeConvNf R root headEqB fuel A B = true then
          some (.convert hu (nbeConvNf_sound R root hHeadEq h))
        else none
      else none

include hHeadEq in
/-- The finitary rule relation `rulesWithNbE` induced by `decodeWithNbE`:
every rule instance is a `FormationSensitiveRuleSignature.Rule R conclusion`
decoded from some `FSCodeWithNbE`. Note that `rulesWithNbE` requires ZERO
completeness assumptions to define or to equip with a `RuleWitness`. -/
def rulesWithNbE (premises : List (Judgment Head)) (conclusion : Judgment Head) : Prop :=
  ∃ (code : FSCodeWithNbE Head conclusion) (rule : Rule R conclusion),
    decodeWithNbE R root headEqB hHeadEq code = some rule ∧
    premises = List.ofFn (hypothesis rule)

include hHeadEq in
/-- **Soundness of `Derives (rulesWithNbE ...)` (unconditional)**:
Every derivation in `rulesWithNbE` is a derivation in `FormationSensitiveChecking.rules R`
and therefore yields `FormationSensitive.Typing R j.context j.subject j.type`. -/
theorem derives_rulesWithNbE_sound {j : Judgment Head}
    (derived : Derives (rulesWithNbE R root headEqB hHeadEq) j) :
    FormationSensitive.Typing R j.context j.subject j.type := by
  apply FormationSensitiveChecking.derives_sound
  refine Derives.mono ?_ derived
  rintro premises conclusion ⟨_, rule, _, hPrem⟩
  exact ⟨rule, hPrem⟩

include hHeadEq in
/-- **Completeness of `Derives (rulesWithNbE ...)` under `TypedConvComplete`**:
Under `UniverseRegularity R` and `TypedConvComplete R root headEqB` (restricted strictly
to `TypedConvObligation`), every `FormationSensitive.Typing R Γ subject type` derivation
in a formed context `Γ` derives `(judgment Γ subject type)` in `rulesWithNbE`. -/
theorem derives_rulesWithNbE_complete_of_typed
    (universes : FormationSensitive.UniverseRegularity R)
    (hComplete : TypedConvComplete R root headEqB)
    {n : Nat} {Γ : Ctx Head n} {subject type : Tm Head n}
    (typing : FormationSensitive.Typing R Γ subject type)
    (formed : FormationSensitive.ContextFormation R Γ) :
    Derives (rulesWithNbE R root headEqB hHeadEq) (judgment Γ subject type) := by
  induction typing with
  | @headType n Γ h u typed =>
      refine .node [] _ ⟨.headType, .headType typed, by simp [decodeWithNbE, typed], rfl⟩ ?_
      intro _ hm; cases hm
  | @var n Γ i =>
      refine .node [] _ ⟨.var i, .var i, rfl, rfl⟩ ?_
      intro _ hm; cases hm
  | @const n Γ name declared u known _ isU ih =>
      have d0 := ih .nil
      refine .node [judgment .nil declared (.head u)] _
        ⟨.const (u := u), .const known isU, by simp [decodeWithNbE, known, isU], rfl⟩ ?_
      intro p hm
      simp only [List.mem_singleton] at hm
      exact hm ▸ d0
  | @piForm n Γ A B u v w tA isU _ isV joined ihA ihB =>
      have dA := ihA formed
      have dB := ihB (.snoc formed tA isU)
      refine .node [judgment Γ A (.head u), judgment (.snoc Γ A) B (.head v)] _
        ⟨.piForm (u := u) (v := v), .piForm isU isV joined,
          by simp [decodeWithNbE, isU, isV, joined], rfl⟩ ?_
      intro p hm
      rcases List.mem_cons.mp hm with rfl | hm'
      · exact dA
      · simp only [List.mem_singleton] at hm'
        exact hm' ▸ dB
  | @sigmaForm n Γ A B u v w tA isU _ isV joined ihA ihB =>
      have dA := ihA formed
      have dB := ihB (.snoc formed tA isU)
      refine .node [judgment Γ A (.head u), judgment (.snoc Γ A) B (.head v)] _
        ⟨.sigmaForm (u := u) (v := v), .sigmaForm isU isV joined,
          by simp [decodeWithNbE, isU, isV, joined], rfl⟩ ?_
      intro p hm
      rcases List.mem_cons.mp hm with rfl | hm'
      · exact dA
      · simp only [List.mem_singleton] at hm'
        exact hm' ▸ dB
  | @lamIntro n Γ A body B u tPi isU _ ihPi ihBody =>
      have dPi := ihPi formed
      obtain ⟨uA, _, _, tA, isUA, _, _, _⟩ := tPi.piFormation
      have dBody := ihBody (.snoc formed tA isUA)
      refine .node [judgment Γ (.pi A B) (.head u), judgment (.snoc Γ A) body B] _
        ⟨.lamIntro (u := u), .lamIntro isU, by simp [decodeWithNbE, isU], rfl⟩ ?_
      intro p hm
      rcases List.mem_cons.mp hm with rfl | hm'
      · exact dPi
      · simp only [List.mem_singleton] at hm'
        exact hm' ▸ dBody
  | @appElim n Γ g a A B _ _ ihG ihA =>
      have dG := ihG formed
      have dA := ihA formed
      refine .node [judgment Γ g (.pi A B), judgment Γ a A] _
        ⟨.appElim (A := A) (B := B), .appElim (A := A) (B := B), rfl, rfl⟩ ?_
      intro p hm
      rcases List.mem_cons.mp hm with rfl | hm'
      · exact dG
      · simp only [List.mem_singleton] at hm'
        exact hm' ▸ dA
  | @pairIntro n Γ a b A B u _ isU _ _ ihSig ihA ihB =>
      have dSig := ihSig formed
      have dA := ihA formed
      have dB := ihB formed
      refine .node [judgment Γ (.sigma A B) (.head u), judgment Γ a A, judgment Γ b (inst0 a B)] _
        ⟨.pairIntro (u := u), .pairIntro isU, by simp [decodeWithNbE, isU], rfl⟩ ?_
      intro p hm
      rcases List.mem_cons.mp hm with rfl | hm1
      · exact dSig
      · rcases List.mem_cons.mp hm1 with rfl | hm2
        · exact dA
        · simp only [List.mem_singleton] at hm2
          exact hm2 ▸ dB
  | @fstElim n Γ p A B _ ihP =>
      have dP := ihP formed
      refine .node [judgment Γ p (.sigma A B)] _
        ⟨.fstElim (B := B), .fstElim (B := B), rfl, rfl⟩ ?_
      intro p' hm
      simp only [List.mem_singleton] at hm
      exact hm ▸ dP
  | @sndElim n Γ p A B _ ihP =>
      have dP := ihP formed
      refine .node [judgment Γ p (.sigma A B)] _
        ⟨.sndElim (A := A) (B := B), .sndElim (A := A) (B := B), rfl, rfl⟩ ?_
      intro p' hm
      simp only [List.mem_singleton] at hm
      exact hm ▸ dP
  | @idForm n Γ A a b u _ isU _ _ ihA iha ihb =>
      have dA := ihA formed
      have da := iha formed
      have db := ihb formed
      refine .node [judgment Γ A (.head u), judgment Γ a A, judgment Γ b A] _
        ⟨.idForm, .idForm isU, by simp [decodeWithNbE, isU], rfl⟩ ?_
      intro p hm
      rcases List.mem_cons.mp hm with rfl | hm1
      · exact dA
      · rcases List.mem_cons.mp hm1 with rfl | hm2
        · exact da
        · simp only [List.mem_singleton] at hm2
          exact hm2 ▸ db
  | @reflIntro n Γ a A _ iha =>
      have da := iha formed
      refine .node [judgment Γ a A] _ ⟨.reflIntro, .reflIntro, rfl, rfl⟩ ?_
      intro p hm
      simp only [List.mem_singleton] at hm
      exact hm ▸ da
  | @cumul n Γ t u v _ order iht =>
      have dt := iht formed
      refine .node [judgment Γ t (.head u)] _
        ⟨.cumul (u := u), .cumul order, by simp [decodeWithNbE, order], rfl⟩ ?_
      intro p hm
      simp only [List.mem_singleton] at hm
      exact hm ▸ dt
  | @conv n Γ t A B u tTerm tB isU converted iht ihB =>
      have dt := iht formed
      have dB := ihB formed
      obtain ⟨uA, isUA, tA⟩ := tTerm.regularity universes formed
      have ob : TypedConvObligation R Γ A B :=
        ⟨formed, ⟨uA, isUA, tA⟩, ⟨u, isU, tB⟩, converted⟩
      obtain ⟨fuel, hFuel⟩ := hComplete ob
      refine .node [judgment Γ t A, judgment Γ B (.head u)] _
        ⟨.convert (A := A) (u := u) fuel,
         .convert isU (nbeConvNf_sound R root hHeadEq hFuel),
         by simp [decodeWithNbE, isU, hFuel], rfl⟩ ?_
      intro p hm
      rcases List.mem_cons.mp hm with rfl | hm'
      · exact dt
      · simp only [List.mem_singleton] at hm'
        exact hm' ▸ dB

include hHeadEq in
/-- **The `RuleWitness` Interface with Verified NbE Conversion (`interfaceWithNbE`)**:
Replaces step-by-step `StructuralConversionCode` in `FormationSensitiveChecking.interface`
with `FSCodeWithNbE` (fuel-bounded `nbeConvNf`). Notice that constructing `interfaceWithNbE`
requires **no completeness assumption** at all. -/
def interfaceWithNbE : RuleWitness (rulesWithNbE R root headEqB hHeadEq) where
  W := (j : Judgment Head) × FSCodeWithNbE Head j
  isInstance witness premises conclusion :=
    match decodeWithNbE R root headEqB hHeadEq witness.2 with
    | none => false
    | some rule => decide (conclusion = witness.1 ∧ premises = List.ofFn (hypothesis rule))
  sound := by
    intro ⟨j, code⟩ premises conclusion accepted
    simp only at accepted
    cases decoded : decodeWithNbE R root headEqB hHeadEq code with
    | none => simp [decoded] at accepted
    | some rule =>
        simp only [decoded, decide_eq_true_eq] at accepted
        obtain ⟨rfl, same⟩ := accepted
        exact ⟨code, rule, decoded, same⟩
  complete := by
    rintro premises conclusion ⟨code, rule, decoded, rfl⟩
    exact ⟨⟨conclusion, code⟩, by simp [decoded]⟩

include hHeadEq in
/-- **Soundness of Graph Replay with Verified NbE (`checked_graph_withNbE_sound`)**:
Unconditional — requires NO completeness assumption. -/
theorem checked_graph_withNbE_sound (j : Judgment Head)
    {nodes : List (DerivationGraph.Node (Judgment Head) (interfaceWithNbE R root headEqB hHeadEq).W Unit)}
    {cache : Array (Judgment Head)} {rootIdx : Nat}
    (hReplay : DerivationGraph.replay (interfaceWithNbE R root headEqB hHeadEq) nodes = some cache)
    (hRoot : cache[rootIdx]? = some j) :
    FormationSensitive.Typing R j.context j.subject j.type :=
  derives_rulesWithNbE_sound R root headEqB hHeadEq
    (DerivationGraph.root_sound (interfaceWithNbE R root headEqB hHeadEq) hReplay hRoot)

include hHeadEq in
/-- **Both-Directions Graph Equivalence (`typing_iff_checked_graph_withNbE`)**:
In any formed context `FormationSensitive.ContextFormation R j.context`, under
`UniverseRegularity R` and `TypedConvComplete R root headEqB` (restricted to
`TypedConvObligation`), `FormationSensitive.Typing` is equivalent to `DerivationGraph.replay`
acceptance over `interfaceWithNbE`. -/
theorem typing_iff_checked_graph_withNbE
    (universes : FormationSensitive.UniverseRegularity R)
    (hComplete : TypedConvComplete R root headEqB)
    (j : Judgment Head)
    (formed : FormationSensitive.ContextFormation R j.context) :
    FormationSensitive.Typing R j.context j.subject j.type ↔
      ∃ (nodes : List (DerivationGraph.Node (Judgment Head) (interfaceWithNbE R root headEqB hHeadEq).W Unit))
        (cache : Array (Judgment Head)) (rootIdx : Nat),
        DerivationGraph.replay (interfaceWithNbE R root headEqB hHeadEq) nodes = some cache ∧
        cache[rootIdx]? = some j := by
  constructor
  · intro typing
    have hDerives :=
      derives_rulesWithNbE_complete_of_typed R root headEqB hHeadEq universes hComplete typing formed
    exact (DerivationGraph.derives_iff_checked_graph
      (interfaceWithNbE R root headEqB hHeadEq) () j).mp hDerives
  · rintro ⟨nodes, cache, rootIdx, hReplay, hRoot⟩
    exact checked_graph_withNbE_sound R root headEqB hHeadEq j hReplay hRoot

include hHeadEq in
/-- **Both-Directions Minted LCF Equivalence (`typing_iff_minted_withNbE`)**:
In any formed context `FormationSensitive.ContextFormation R j.context`, under
`UniverseRegularity R` and `TypedConvComplete R root headEqB` (restricted to
`TypedConvObligation`), `FormationSensitive.Typing` is equivalent to
`DerivationGraph.CheckedJudgment.mint` over `interfaceWithNbE`. -/
theorem typing_iff_minted_withNbE
    (universes : FormationSensitive.UniverseRegularity R)
    (hComplete : TypedConvComplete R root headEqB)
    (j : Judgment Head)
    (formed : FormationSensitive.ContextFormation R j.context) :
    FormationSensitive.Typing R j.context j.subject j.type ↔
      ∃ (nodes : List (DerivationGraph.Node (Judgment Head) (interfaceWithNbE R root headEqB hHeadEq).W Unit))
        (rootIdx : Nat),
        (DerivationGraph.CheckedJudgment.mint (interfaceWithNbE R root headEqB hHeadEq) nodes rootIdx).map
          DerivationGraph.CheckedJudgment.judgment = some j := by
  constructor
  · intro typing
    have hDerives :=
      derives_rulesWithNbE_complete_of_typed R root headEqB hHeadEq universes hComplete typing formed
    exact (DerivationGraph.CheckedJudgment.exists_mint_iff
      (interfaceWithNbE R root headEqB hHeadEq) () j).mpr hDerives
  · rintro ⟨nodes, rootIdx, hMint⟩
    obtain ⟨cache, hReplay, hRoot⟩ :=
      (DerivationGraph.CheckedJudgment.mint_iff
        (interfaceWithNbE R root headEqB hHeadEq) nodes rootIdx j).mp hMint
    exact checked_graph_withNbE_sound R root headEqB hHeadEq j hReplay hRoot

include hHeadEq in
/-- Public request checker combining context formation (`checkContextWithNbE`)
and `CheckedJudgment.mint` over `interfaceWithNbE` (requiring NO `hComplete` parameter). -/
def checkRequestWithNbE
    (j : Judgment Head) (context : ContextCodeWithNbE Head j.arity)
    (nodes : List (DerivationGraph.Node (Judgment Head) (interfaceWithNbE R root headEqB hHeadEq).W Unit))
    (rootIdx : Nat) : Bool :=
  checkContextWithNbE R root headEqB j.context context && decide
    ((DerivationGraph.CheckedJudgment.mint (interfaceWithNbE R root headEqB hHeadEq) nodes rootIdx).map
      DerivationGraph.CheckedJudgment.judgment = some j)

include hHeadEq in
/-- **Soundness of `checkRequestWithNbE` (unconditional)**: -/
theorem checkRequestWithNbE_sound
    (j : Judgment Head) (context : ContextCodeWithNbE Head j.arity)
    (nodes : List (DerivationGraph.Node (Judgment Head) (interfaceWithNbE R root headEqB hHeadEq).W Unit))
    (rootIdx : Nat)
    (accepted : checkRequestWithNbE R root headEqB hHeadEq j context nodes rootIdx = true) :
    FormationSensitive.Judgment R j.context j.subject j.type := by
  simp only [checkRequestWithNbE, Bool.and_eq_true, decide_eq_true_eq] at accepted
  obtain ⟨cache, replayed, found⟩ :=
    (DerivationGraph.CheckedJudgment.mint_iff
      (interfaceWithNbE R root headEqB hHeadEq) nodes rootIdx j).mp accepted.2
  exact ⟨checkContextWithNbE_sound R root headEqB hHeadEq accepted.1,
    checked_graph_withNbE_sound R root headEqB hHeadEq j replayed found⟩

include hHeadEq in
/-- **Both-Directions Request Coverage (`judgment_iff_checkedRequestWithNbE`)**:
Under `UniverseRegularity R` and `TypedConvComplete R root headEqB` (restricted strictly
to `TypedConvObligation`), `FormationSensitive.Judgment R j.context j.subject j.type`
holds if and only if there exist `context`, `nodes`, and `rootIdx` accepted by
`checkRequestWithNbE`. -/
theorem judgment_iff_checkedRequestWithNbE
    (universes : FormationSensitive.UniverseRegularity R)
    (hComplete : TypedConvComplete R root headEqB)
    (j : Judgment Head) :
    FormationSensitive.Judgment R j.context j.subject j.type ↔
      ∃ (context : ContextCodeWithNbE Head j.arity)
        (nodes : List (DerivationGraph.Node (Judgment Head) (interfaceWithNbE R root headEqB hHeadEq).W Unit))
        (rootIdx : Nat),
        checkRequestWithNbE R root headEqB hHeadEq j context nodes rootIdx = true := by
  constructor
  · intro derived
    obtain ⟨context, checkedContext⟩ :=
      checkContextWithNbE_complete_of_typed R root headEqB universes hComplete derived.context
    obtain ⟨nodes, rootIdx, minted⟩ :=
      (typing_iff_minted_withNbE R root headEqB hHeadEq universes hComplete j derived.context).mp
        derived.typing
    exact ⟨context, nodes, rootIdx, by simp [checkRequestWithNbE, checkedContext, minted]⟩
  · rintro ⟨context, nodes, rootIdx, checked⟩
    exact checkRequestWithNbE_sound R root headEqB hHeadEq j context nodes rootIdx checked

/-- The formation-sensitive judgment checker accepts indexed tree evidence.
Its cost and a native pattern codec are separate interfaces. -/
def nbeJudgmentChecker :
    Checker (Judgment Head)
      (Σ j : Judgment Head, ContextCodeWithNbE Head j.arity × CodeWithNbE Head j.arity) where
  check j cert :=
    if h : cert.1 = j then
      checkJudgmentWithNbE R root headEqB j.context j.subject j.type
        (h ▸ cert.2.1) (h ▸ cert.2.2)
    else false

include hHeadEq in
/-- Every accepted tree certificate establishes its complete formed judgment. -/
theorem nbeJudgmentChecker_sound :
    (nbeJudgmentChecker R root headEqB).Sound
      (fun j => FormationSensitive.Judgment R j.context j.subject j.type) := by
  intro j ⟨j', cCode, tCode⟩ hCheck
  dsimp [nbeJudgmentChecker] at hCheck
  split at hCheck
  · rename_i hEq
    subst hEq
    exact checkJudgmentWithNbE_sound R root headEqB hHeadEq hCheck
  · contradiction

include hHeadEq in
/-- Sound replay and complete certificate coverage use the same checker and
judgment. Conversion completeness is required only for evidence coverage. -/
theorem nbeJudgmentChecker_authority
    (universes : FormationSensitive.UniverseRegularity R)
    (hComplete : TypedConvComplete R root headEqB) :
    (nbeJudgmentChecker R root headEqB).Authority
      (fun j => FormationSensitive.Judgment R j.context j.subject j.type) where
  sound := nbeJudgmentChecker_sound R root headEqB hHeadEq
  complete := by
    intro j derived
    obtain ⟨contextCode, termCode, checked⟩ :=
      (judgment_iff_checkedReplayWithNbE R root headEqB hHeadEq universes hComplete).mp derived
    exact ⟨⟨j, contextCode, termCode⟩, by simp [nbeJudgmentChecker, checked]⟩

include hHeadEq in
/-- Formed judgments coincide with the existence of accepted tree evidence. -/
theorem nbeJudgmentChecker_iff
    (universes : FormationSensitive.UniverseRegularity R)
    (hComplete : TypedConvComplete R root headEqB) (j : Judgment Head) :
    FormationSensitive.Judgment R j.context j.subject j.type ↔
      ∃ certificate, (nbeJudgmentChecker R root headEqB).check j certificate = true :=
  (nbeJudgmentChecker_authority R root headEqB hHeadEq universes hComplete).meaning_iff_exists_certificate j

end NIKStageALink

/-! ## Positive and separating negative controls -/

section Controls

open TowerNumbersModel

/-- Universe sort `U_k` in `Tower`. -/
def uSort {n : Nat} (k : Nat) : Tower.Tm n := .head (.sort (.const k))

/-- Opaque ground constant `legacyGround : U_0` in `Tower`. -/
def groundTm {n : Nat} : Tower.Tm n := .head .legacyGround

/-! ### Positive Controls -/

/-- **Positive Control 1 (Π-η Conversion)**:
In context `Γ = [f : Π (x : U0), U0]`, the NbE bidirectional equality checker
accepts `f ≡ (λ x. f x) : Π (x : U0), U0`. -/
theorem positive_control_pi_eta :
    let piTy : Tower.Tm 0 := .pi (uSort 0) (uSort 0)
    let ctx : Tower.Ctx 1 := .snoc .nil piTy
    let lhs : Tower.Tm 1 := .var 0
    let rhs : Tower.Tm 1 := etaExpandPiTm (.var 0)
    towerNbEAcceptsEquality 40 ctx lhs rhs (.pi (uSort 0) (uSort 0)) = true := by
  decide +kernel

/-- Consequently, `f` and `λ x. f x` are declaratively equal in `Equal Tower.rules`. -/
theorem positive_control_pi_eta_equal :
    let piTy : Tower.Tm 0 := .pi (uSort 0) (uSort 0)
    let ctx : Tower.Ctx 1 := .snoc .nil piTy
    Equal Tower.rules ctx (.var 0) (etaExpandPiTm (.var 0)) (.pi (uSort 0) (uSort 0)) :=
  towerNbEAcceptsEquality_sound positive_control_pi_eta

/-- **Positive Control 2 (Σ-η Conversion)**:
In context `Γ = [p : Σ (x : U0), U0]`, the NbE bidirectional equality checker
accepts `p ≡ (fst p, snd p) : Σ (x : U0), U0`. -/
theorem positive_control_sigma_eta :
    let sigmaTy : Tower.Tm 0 := .sigma (uSort 0) (uSort 0)
    let ctx : Tower.Ctx 1 := .snoc .nil sigmaTy
    let lhs : Tower.Tm 1 := .var 0
    let rhs : Tower.Tm 1 := etaExpandSigmaTm (.var 0)
    towerNbEAcceptsEquality 40 ctx lhs rhs (.sigma (uSort 0) (uSort 0)) = true := by
  decide +kernel

/-- Consequently, `p` and `(fst p, snd p)` are declaratively equal in `Equal Tower.rules`. -/
theorem positive_control_sigma_eta_equal :
    let sigmaTy : Tower.Tm 0 := .sigma (uSort 0) (uSort 0)
    let ctx : Tower.Ctx 1 := .snoc .nil sigmaTy
    Equal Tower.rules ctx (.var 0) (etaExpandSigmaTm (.var 0)) (.sigma (uSort 0) (uSort 0)) :=
  towerNbEAcceptsEquality_sound positive_control_sigma_eta

/-- **Positive Control 3 (Universe Cumulativity and Polymorphic Identity)**:
`U0 : U3` and `λ A x. x : Π (A : U0), A → A` are both accepted by `towerNbEAccepts`. -/
theorem positive_control_cumulativity_and_poly_id :
    towerNbEAccepts 40 .nil (uSort 0) (uSort 3) = true ∧
    towerNbEAccepts 40 .nil (.lam (.lam (.var 0)))
      (.pi (uSort 0) (.pi (.var 0) (.var 1))) = true := by
  decide +kernel

/-- The accepted polymorphic identity has its declarative dependent type. -/
theorem polymorphic_identity_typed :
    Typed Tower.rules .nil (.lam (.lam (.var 0)))
      (.pi (uSort 0) (.pi (.var 0) (.var 1))) :=
  towerNbEAccepts_sound positive_control_cumulativity_and_poly_id.2

/-- The complete raw checker applies to this formed expected type. -/
theorem polymorphic_identity_check_complete :
    ∃ fuel, (towerNbECheck fuel .nil (.lam (.lam (.var 0)))
      (.pi (uSort 0) (.pi (.var 0) (.var 1)))).isSome := by
  exact (tower_typed_iff_exists_fuel_nbeCheck
    (.lam (.lam (.synthesized (.var 0)))) .nil
    (Typed.isType (S := TowerModel.setting (fun _ => 0)) polymorphic_identity_typed .nil)).mp
      polymorphic_identity_typed

/-- Full judgment completeness computes formation for the same dependent example. -/
theorem polymorphic_identity_judgment_complete :
    ∃ fuel, towerNbEAccepts fuel .nil (.lam (.lam (.var 0)))
      (.pi (uSort 0) (.pi (.var 0) (.var 1))) = true := by
  exact (tower_typed_iff_exists_fuel_nbeAccepts .nil
    (.pi (.head _) (.pi (.var 0) (.var 1)))
    (.lam (.lam (.synthesized (.var 0))))).mp ⟨.nil, polymorphic_identity_typed⟩

/-- **Positive Control 4 (Recursor ι-Unfolding via Closure-Based NbE)**:
The closure-based NbE machine `nbeNormTm` normalizes `copiedByRecursor 3` to
`numeral 3`, and `towerNumbersNbEAcceptsEquality` accepts
`copiedByRecursor 3 ≡ numeral 3 : num`. -/
theorem positive_control_recursor_nbe :
    let lvl : LevelExpr Nat := .const 0
    nbeNormTm (TowerNumbersModel.rules lvl) (ExecutableTowerNumbers.root lvl) 40
      (ExecutableCheckingControls.copiedByRecursor 3) =
      some (ExecutableCheckingControls.numeral 3) ∧
    towerNumbersNbEAcceptsEquality lvl 60 .nil
      (ExecutableCheckingControls.copiedByRecursor 3)
      (ExecutableCheckingControls.numeral 3)
      ExecutableCheckingControls.num = true := by
  decide +kernel

/-- **Positive Control 5 (Long β-Chain Conversion via Verified NbE with Zero Step Certificates)**:
`nbeConvNf` establishes `idBetaChain 8 (uSort 0) ≡ uSort 0` with `fuel = 30` and
zero step-by-step conversion certificates, whereas `StructuralConversionCode`
requires an 8-step certificate chain. -/
theorem positive_control_betaChain_nbeConv :
    nbeConvNf Tower.rules (fun _ => none)
      (fun h₁ h₂ => decide (h₁ = h₂ ∨ Tower.HeadEq h₁ h₂))
      30 (Separation.idBetaChain 8 (uSort 0 : Tower.Tm 0)) (uSort 0) = true := by
  decide +kernel

theorem positive_control_betaChain_conv :
    Conv Tower.HeadEq (Separation.idBetaChain 8 (uSort 0 : Tower.Tm 0)) (uSort 0) :=
  nbeConvNf_sound Tower.rules (fun _ => none)
    (fun _ _ h => of_decide_eq_true h) positive_control_betaChain_nbeConv

/-! ### Negative Controls (Executable Rejection & Declarative `¬ Typed` Refutations) -/

/-- **General Declarative Universe-Hierarchy Refutation (`tower_not_typed_uSort_of_le`)**:
Whenever `m ≤ k`, universe `U_k` (`uSort k`) does NOT have type `U_m` (`uSort m`)
in any formed context `Γ` of `Tower.rules`:
`¬ Typed Tower.rules Γ (uSort k) (uSort m)`. -/
theorem tower_not_typed_uSort_of_le {n : Nat} {Γ : Tower.Ctx n}
    (formed : CtxFormed Tower.rules Γ) {k m : Nat} (hle : m ≤ k) :
    ¬ Typed Tower.rules Γ (uSort k) (uSort m) := by
  have hSynth : Synth Tower.rules (fun _ => .rigid) Γ (uSort k) (.head (.sort (.succ (.const k)))) :=
    .head (.sort (.const k))
  apply Synth.not_typed (S := TowerModel.setting (fun _ => 0))
    TowerModel.facts TowerModel.algebra levelTower_headsTyped hSynth formed
  intro hBelow
  obtain ⟨v, _, eB, hCumul⟩ :=
    (Below.universe_iff (S := TowerModel.setting (fun _ => 0))
      TowerModel.facts TowerModel.algebra formed (.sort (.succ (.const k)))).1 hBelow
  have hSame :=
    TypeEq.head_injective TowerModel.facts eB formed
  have hCumul₀ : Tower.rules.cumulative (.sort (.succ (.const k))) (.sort (.const m)) :=
    TowerModel.algebra.same_right hCumul (HeadSame.symm (TowerModel.levels (fun _ => 0)) hSame)
  have hEval := hCumul₀ (fun _ => 0)
  change k + 1 ≤ m at hEval
  omega

/-- **Negative Control 1 (`Type : Type` / `U0 : U0` Rejected — Executable & Declarative)**:
`U0 : U0` is rejected by `towerNbEAccepts` AND declaratively refuted (`¬ Typed`). -/
theorem negative_control_self_universe_rejected :
    towerNbEAccepts 40 .nil (uSort 0) (uSort 0) = false := by
  decide +kernel

theorem negative_control_self_universe_not_typed :
    ¬ Typed Tower.rules .nil (uSort 0) (uSort 0) :=
  tower_not_typed_uSort_of_le .nil (Nat.le_refl 0)

/-- **Negative Control 2 (Ill-Typed Application Rejected — Executable & Declarative)**:
Applying the non-function `groundTm : U0` to `groundTm` is rejected by `towerNbEAccepts`
AND declaratively has no type (`∀ X, ¬ Typed Tower.rules .nil (.app groundTm groundTm) X`),
even when buried inside an unused lambda argument `(λ _. uSort 0) (groundTm groundTm)`. -/
theorem negative_control_ill_typed_app_rejected :
    towerNbEAccepts 40 .nil (.app groundTm groundTm) (uSort 0) = false ∧
    towerNbEAccepts 40 .nil (.app (.lam (uSort 0 : Tower.Tm 1)) (.app groundTm groundTm))
      (uSort 1) = false := by
  decide +kernel

theorem negative_control_ill_typed_app_not_typed (X : Tower.Tm 0) :
    ¬ Typed Tower.rules .nil (.app groundTm groundTm) X := by
  have hSynth : Synth Tower.rules (fun _ => .rigid) .nil groundTm (.head (.sort LevelTower.zero)) :=
    .head .legacyGround
  have hRed : RedTy Tower.rules (fun _ => .rigid) .nil
      (.head (.sort LevelTower.zero)) (.head (.sort LevelTower.zero)) :=
    RedTy.refl (roles := fun _ => .rigid)
      (⟨.sort (.succ LevelTower.zero), LevelTower.IsUniverse.sort _,
        (.headType (LevelTower.HeadTyping.sort _))⟩ : IsType Tower.rules .nil
          (.head (.sort LevelTower.zero)))
  exact Synth.not_applicable (S := TowerModel.setting (fun _ => 0))
    TowerModel.facts TowerModel.algebra levelTower_headsTyped
    hSynth .nil hRed (.inl ⟨_, rfl⟩) (fun _ _ h => by cases h)

theorem negative_control_unused_ill_typed_arg_not_typed (X : Tower.Tm 0) :
    ¬ Typed Tower.rules .nil (.app (.lam (uSort 0 : Tower.Tm 1)) (.app groundTm groundTm)) X := by
  intro typing
  obtain ⟨A', _, _, ta, _⟩ := Typed.generation typing
  exact negative_control_ill_typed_app_not_typed A' ta

/-- A reducible expected expression can hide an ill-typed argument. -/
def unformedExpectedType : Tower.Tm 0 :=
  .app (.lam (uSort 1)) (.app groundTm groundTm)

/-- Raw term checking assumes an expected type; full judgment checking validates it. -/
theorem raw_check_does_not_check_expected_formation :
    (towerNbECheck 60 .nil (uSort 0) unformedExpectedType).isSome = true ∧
      towerNbEAccepts 60 .nil (uSort 0) unformedExpectedType = false := by
  decide +kernel

/-- The rejected expected expression has no universe type, independently of fuel. -/
theorem unformedExpectedType_not_isType :
    ¬ IsType Tower.rules .nil unformedExpectedType := by
  rintro ⟨u, _, typing⟩
  obtain ⟨A, _, _, argument, _⟩ := Typed.generation typing
  exact negative_control_ill_typed_app_not_typed A argument

/-- **Negative Control 3 (Universe Lowering Rejected — Executable & Declarative)**:
Checking `U1` (`uSort 1`) at `U0` or at `U1` is rejected by `towerNbEAccepts`
AND declaratively refuted (`¬ Typed Tower.rules .nil (uSort 1) (uSort 0) ∧ ¬ Typed Tower.rules .nil (uSort 1) (uSort 1)`). -/
theorem negative_control_universe_lowering_rejected :
    towerNbEAccepts 40 .nil (uSort 1) (uSort 0) = false ∧
    towerNbEAccepts 40 .nil (uSort 1) (uSort 1) = false := by
  decide +kernel

theorem negative_control_universe_lowering_not_typed :
    ¬ Typed Tower.rules .nil (uSort 1) (uSort 0) ∧
    ¬ Typed Tower.rules .nil (uSort 1) (uSort 1) :=
  ⟨tower_not_typed_uSort_of_le .nil (Nat.zero_le 1),
   tower_not_typed_uSort_of_le .nil (Nat.le_refl 1)⟩

/-- **Negative Control 4 (Near-Miss Dependent Pair and Identity Endpoint Rejected — Executable & Declarative)**:
The near-miss dependent pair `wrongPack = λ x. (x, refl (succ x))` against
`packType = Π (n : Nat), Σ (m : Nat), Id Nat n m` and the mismatched reflexivity proof
`refl 0 : Id Nat 0 1` are both rejected by `towerNumbersNbEAccepts` AND declaratively
refuted (`¬ Typed (TowerNumbersModel.rules lv) ...`). -/
theorem negative_control_near_miss_pair_and_id_rejected :
    let lvl : LevelExpr Nat := .const 0
    towerNumbersNbEAccepts lvl 60 .nil
      ExecutableCheckingControls.wrongPack
      ExecutableCheckingControls.packType = false ∧
    towerNumbersNbEAccepts lvl 60 .nil
      (.refl ExecutableCheckingControls.zero)
      (.id ExecutableCheckingControls.num
        ExecutableCheckingControls.zero
        (ExecutableCheckingControls.succ ExecutableCheckingControls.zero)) = false := by
  decide +kernel

theorem negative_control_zero_ne_succ :
    ¬ Equal (TowerNumbersModel.rules (.const 0)) .nil
        ExecutableCheckingControls.zero
        (ExecutableCheckingControls.succ ExecutableCheckingControls.zero)
        ExecutableCheckingControls.num :=
  TowerNumbers.zero_ne_succ .nil

/-- Declarative refutation: `refl 0` does NOT have type `Id num 0 (succ 0)`. -/
theorem negative_control_refl_zero_succ_not_typed (lv : LevelExpr Nat) :
    ¬ Typed (TowerNumbersModel.rules lv) .nil
        (.refl ExecutableCheckingControls.zero)
        (.id ExecutableCheckingControls.num
          ExecutableCheckingControls.zero
          (ExecutableCheckingControls.succ ExecutableCheckingControls.zero)) := by
  intro typing
  let S := TowerNumbersModel.setting lv (fun _ => 0)
  obtain ⟨A, _, le⟩ := Typed.generation typing
  have isE := Typed.isType (S := S) typing .nil
  have e := TypeLe.id_eq (S := S) (TowerNumbersModel.facts lv) le isE .nil
  obtain ⟨eA, _, ey⟩ := TypeEq.id_injective (TowerNumbersModel.facts lv) e .nil
  have eq01 : Equal (TowerNumbersModel.rules lv) .nil
      ExecutableCheckingControls.zero
      (ExecutableCheckingControls.succ ExecutableCheckingControls.zero)
      ExecutableCheckingControls.num :=
    Equal.convType ey eA
  exact TowerNumbers.zero_ne_succ .nil eq01

/-- Declarative refutation: `wrongPack = λ x. (x, refl (succ x))` does NOT have
type `packType = Π (n : num), Σ (m : num), Id num n m`. -/
theorem negative_control_wrongPack_not_typed (lv : LevelExpr Nat) :
    ¬ Typed (TowerNumbersModel.rules lv) .nil
        ExecutableCheckingControls.wrongPack
        ExecutableCheckingControls.packType := by
  intro tWrong
  let S := TowerNumbersModel.setting lv (fun _ => 0)
  have tNum : Typed (TowerNumbersModel.rules lv) .nil
      ExecutableCheckingControls.num (.head TowerNumbersModel.u) :=
    TowerNumbersModel.num_typed LevelTower.HeadTyping.sort LevelTower.IsUniverse.sort
      (TowerNumbersModel.declaredNum lv)
  have tZero : Typed (TowerNumbersModel.rules lv) .nil
      ExecutableCheckingControls.zero ExecutableCheckingControls.num :=
    .const (TowerNumbersModel.declaredZero lv) tNum (.sort _)
  have tApp : Typed (TowerNumbersModel.rules lv) .nil
      (.app ExecutableCheckingControls.wrongPack ExecutableCheckingControls.zero)
      (.sigma ExecutableCheckingControls.num
        (.id ExecutableCheckingControls.num ExecutableCheckingControls.zero (.var 0))) :=
    .appElim tWrong tZero
  have hStep : Reduces (TowerNumbersModel.rules lv)
      (.app ExecutableCheckingControls.wrongPack ExecutableCheckingControls.zero)
      (.pair ExecutableCheckingControls.zero
        (.refl (ExecutableCheckingControls.succ ExecutableCheckingControls.zero))) :=
    .single (.betaPi (.pair (.var 0) (.refl (ExecutableCheckingControls.succ (.var 0))))
      ExecutableCheckingControls.zero)
  obtain ⟨tPair, _⟩ := TowerNumbers.reduces_preserve .nil hStep tApp
  obtain ⟨A, B, _, _, _, ta, tb, leSigma⟩ := Typed.generation tPair
  obtain ⟨_, leB⟩ := TypeLe.sigma_parts (S := S) (TowerNumbersModel.facts lv)
    leSigma (Typed.isType tPair .nil) .nil
  have leB0 : Below (TowerNumbersModel.rules lv) .nil (inst0 ExecutableCheckingControls.zero B)
      (.id ExecutableCheckingControls.num
        ExecutableCheckingControls.zero ExecutableCheckingControls.zero) :=
    Derivable.substitutes leB (SubstMor.single ta)
  have tRefl : Typed (TowerNumbersModel.rules lv) .nil
      (.refl (ExecutableCheckingControls.succ ExecutableCheckingControls.zero))
      (.id ExecutableCheckingControls.num
        ExecutableCheckingControls.zero ExecutableCheckingControls.zero) :=
    .sub tb leB0
  obtain ⟨C, _, leId⟩ := Typed.generation tRefl
  have eId := TypeLe.id_eq (S := S) (TowerNumbersModel.facts lv)
    leId (Typed.isType tRefl .nil) .nil
  obtain ⟨eC, ex, _⟩ := TypeEq.id_injective (TowerNumbersModel.facts lv) eId .nil
  have eq10 : Equal (TowerNumbersModel.rules lv) .nil
      (ExecutableCheckingControls.succ ExecutableCheckingControls.zero)
      ExecutableCheckingControls.zero
      ExecutableCheckingControls.num :=
    Equal.convType ex eC
  exact TowerNumbers.zero_ne_succ .nil (.symm eq10)

end Controls

/-! ## Instrumented beta-chain and certificate-size comparison -/

section PerformanceComparison

/-- Construct the explicit `k`-step `StructuralConversionCode` required to witness
`idBetaChain k t ≡ t` in the step-by-step replay tier. Its size is $k$ step nodes. -/
def idBetaChainConvCode {Head : Type} {RootCode : Nat → Type} {n : Nat}
    (t : Tm Head n) : (k : Nat) → StructuralConversionCode.Code Head RootCode n
  | 0 => .refl t
  | k + 1 =>
      .trans
        (.single (.betaPi (.var 0) (Separation.idBetaChain k t)))
        (idBetaChainConvCode t k)

/-- Count the number of conversion step nodes in a `StructuralConversionCode.Code`. -/
def convCodeStepCount {Head : Type} {RootCode : Nat → Type} {n : Nat} :
    StructuralConversionCode.Code Head RootCode n → Nat
  | .refl _ => 0
  | .single _ => 1
  | .symm c => convCodeStepCount c
  | .trans c₁ c₂ => convCodeStepCount c₁ + convCodeStepCount c₂

/-- The step-by-step conversion certificate `idBetaChainConvCode t k` has
exact size `k` steps ($O(k)$ step nodes and $\Theta(k^2)$ AST certificate size
`codeCertSize`), whereas the verified NbE rung carries `0` step certificates. -/
theorem convCodeStepCount_idBetaChain {Head : Type} {RootCode : Nat → Type} {n : Nat}
    (t : Tm Head n) (k : Nat) :
    convCodeStepCount (idBetaChainConvCode (RootCode := RootCode) t k) = k := by
  induction k with
  | zero => rfl
  | succ m ih =>
      simp [idBetaChainConvCode, convCodeStepCount, ih, Nat.add_comm]

/-- On `idBetaChain k groundTm`, the instrumented closure machine `nbeWhnfSteps`
returns `some (3 * k + 1)` evaluation steps ($O(k)$ time), while `codeCertSize` of the
explicit certificate `idBetaChainCode k groundTm` is $3k(k+1)/2 + 2k + 1$ ($\Theta(k^2)$). -/
theorem nbeWhnfSteps_idBetaChain_groundTm (k : Nat) :
    nbeWhnfSteps Tower.rules (fun _ => none) (2 * k + 1)
      (Separation.idBetaChain k (groundTm : Tower.Tm 0)) = some (3 * k + 1) := by
  unfold nbeWhnfSteps
  have fuel : 2 * k + 1 = 1 + 2 * k := by omega
  rw [fuel, Separation.whEvalSteps_idBetaChain Tower.rules (fun _ => none)
    k 1 (WhEnv.idEnv 0) (groundTm : Tower.Tm 0)]
  rfl

/-- Benchmark row recording:
1. chain length `k`,
2. NbE conversion acceptance `nbeOk`,
3. explicit replay acceptance `replayOk`,
4. instrumented NbE machine step count `nbeSteps = some (3 * k + 1)` ($O(k)$ time),
5. conversion step count `stepNodes = k`,
6. total explicit certificate AST size `explicitCertNodes = 3k(k+1)/2 + 2k + 1` ($\Theta(k^2)$ size),
7. NbE per-run conversion certificate size `nbeCertNodes = 0`. -/
def betaChainBenchmarkRow (k : Nat) : Nat × Bool × Bool × Option Nat × Nat × Nat × Nat :=
  let lhs : Tower.Tm 0 := Separation.idBetaChain k groundTm
  let rhs : Tower.Tm 0 := groundTm
  let code : StructuralConversionCode.Code Tower.Head (fun _ => Empty) 0 :=
    Separation.idBetaChainCode k rhs
  let nbeOk :=
    nbeConvNf Tower.rules (fun _ => none)
      (fun h₁ h₂ => decide (h₁ = h₂ ∨ Tower.HeadEq h₁ h₂))
      (2 * k + 5) lhs rhs
  let replayChecker :=
    Separation.explicitConversionSizedChecker Tower.HeadEq 0
  let replayOk := replayChecker.check ⟨lhs, rhs⟩ code
  let nbeSteps := nbeWhnfSteps Tower.rules (fun _ => none) (2 * k + 1) lhs
  let stepNodes := convCodeStepCount code
  let explicitCertNodes := replayChecker.certificateSize code
  let nbeCertNodes := 0
  (k, nbeOk, replayOk, nbeSteps, stepNodes, explicitCertNodes, nbeCertNodes)

theorem nbe_and_syntactic_agree_on_betaChains :
    List.map betaChainBenchmarkRow [1, 2, 4, 8, 12, 16] =
    [(1, true, true, some 4, 1, 6, 0),
     (2, true, true, some 7, 2, 17, 0),
     (4, true, true, some 13, 4, 57, 0),
     (8, true, true, some 25, 8, 209, 0),
     (12, true, true, some 37, 12, 457, 0),
     (16, true, true, some 49, 16, 801, 0)] := by
  rfl

#eval List.map betaChainBenchmarkRow [1, 2, 4, 8, 12, 16]

/-- Executable regressions for dependent checking, formation boundaries and
instrumented closure evaluation. -/
def checkingVerdicts : List (String × Bool) :=
  let piTy : Tower.Tm 0 := .pi (uSort 0) (uSort 0)
  let sigmaTy : Tower.Tm 0 := .sigma (uSort 0) (uSort 0)
  let lv : LevelExpr Nat := .const 0
  [("NbE Pi eta", towerNbEAcceptsEquality 40 (.snoc .nil piTy)
      (.var 0) (etaExpandPiTm (.var 0)) (.pi (uSort 0) (uSort 0))),
   ("NbE Sigma eta", towerNbEAcceptsEquality 40 (.snoc .nil sigmaTy)
      (.var 0) (etaExpandSigmaTm (.var 0)) (.sigma (uSort 0) (uSort 0))),
   ("NbE cumulative universe", towerNbEAccepts 40 .nil (uSort 0) (uSort 3)),
   ("NbE polymorphic identity", towerNbEAccepts 40 .nil (.lam (.lam (.var 0)))
      (.pi (uSort 0) (.pi (.var 0) (.var 1)))),
   ("NbE natural recursor", towerNumbersNbEAcceptsEquality lv 60 .nil
      (ExecutableCheckingControls.copiedByRecursor 3)
      (ExecutableCheckingControls.numeral 3) ExecutableCheckingControls.num),
   ("NbE beta chain conversion", nbeConvNf Tower.rules (fun _ => none)
      (fun first second => decide (first = second ∨ Tower.HeadEq first second))
      30 (Separation.idBetaChain 8 (uSort 0 : Tower.Tm 0)) (uSort 0)),
   ("NbE self universe refused", !(towerNbEAccepts 40 .nil (uSort 0) (uSort 0))),
   ("NbE ill typed application refused", !(towerNbEAccepts 40 .nil
      (.app groundTm groundTm) (uSort 0))),
   ("NbE universe lowering refused", !(towerNbEAccepts 40 .nil (uSort 1) (uSort 0))),
   ("NbE dependent pair mismatch refused", !(towerNumbersNbEAccepts lv 60 .nil
      ExecutableCheckingControls.wrongPack ExecutableCheckingControls.packType)),
   ("NbE identity endpoint mismatch refused", !(towerNumbersNbEAccepts lv 60 .nil
      (.refl ExecutableCheckingControls.zero)
      (.id ExecutableCheckingControls.num ExecutableCheckingControls.zero
        (ExecutableCheckingControls.succ ExecutableCheckingControls.zero)))),
   ("NbE raw check assumes formed expected type", (towerNbECheck 60 .nil
      (uSort 0) unformedExpectedType).isSome),
   ("NbE full judgment refuses unformed expected type", !(towerNbEAccepts 60 .nil
      (uSort 0) unformedExpectedType)),
   ("NbE exhausted fuel retains no cost", (nbeWhnfSteps Tower.rules (fun _ => none) 1
      (Separation.idBetaChain 2 (groundTm : Tower.Tm 0))).isNone)] ++
    [1, 2, 4, 8, 12, 16].map (fun k =>
      (s!"NbE beta chain {k} exact steps", match nbeWhnfSteps Tower.rules (fun _ => none)
          (2 * k + 1) (Separation.idBetaChain k (groundTm : Tower.Tm 0)) with
        | none => false
        | some steps => steps == 3 * k + 1))

/-- The executable panel agrees with the checked positive and separating controls. -/
theorem checkingVerdicts_all : checkingVerdicts.all Prod.snd = true := by
  decide +kernel

end PerformanceComparison

#print axioms nbeJudgmentChecker_sound
#print axioms nbeJudgmentChecker_authority
#print axioms raw_check_does_not_check_expected_formation
#print axioms unformedExpectedType_not_isType
#print axioms nbeWhnfSteps_idBetaChain_groundTm
#print axioms towerNbEAccepts_sound
#print axioms towerNbEAcceptsEquality_sound
#print axioms tower_typed_iff_exists_fuel_nbeCheck
#print axioms tower_typable_iff_exists_fuel_nbeSynth
#print axioms tower_typed_iff_exists_fuel_nbeAccepts
#print axioms tower_equal_iff_exists_fuel_nbeAcceptsEquality
#print axioms checkReplayWithNbE_sound
#print axioms judgment_iff_checkedReplayWithNbE
#print axioms typing_iff_checked_graph_withNbE
#print axioms typing_iff_minted_withNbE
#print axioms judgment_iff_checkedRequestWithNbE
#print axioms positive_control_pi_eta_equal
#print axioms positive_control_sigma_eta_equal
#print axioms positive_control_betaChain_conv
#print axioms negative_control_self_universe_not_typed
#print axioms negative_control_ill_typed_app_not_typed
#print axioms negative_control_universe_lowering_not_typed
#print axioms negative_control_refl_zero_succ_not_typed
#print axioms negative_control_wrongPack_not_typed
#print axioms negative_control_zero_ne_succ

end Mettapedia.TypeTheory.NbE
