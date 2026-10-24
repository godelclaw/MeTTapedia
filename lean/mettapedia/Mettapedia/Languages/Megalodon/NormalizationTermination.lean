import Mettapedia.Languages.Megalodon.RetainedNormalization
import Mettapedia.Logic.HOL.BetaEtaNormalization
import Mettapedia.Languages.Megalodon.DeltaNormalInvariant

/-!
# Termination of Megalodon's typed monomorphic normalization

The intrinsic pass already computes retained equality proofs. Here its actual
targets and stability flags are related to typed beta/eta reduction. A changed
pass must make genuine reduction progress; ordinary equality alone would not
justify terminating the iteration.

Accessibility computes a sufficient budget for the existing native beta/eta
algorithm. The full native pipeline has the same guarantee on a term with no
expandable declaration in its support. Recursive definitions and prefix type
computation remain separate boundaries.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.Megalodon.NormalizationTermination

open Mettapedia.Logic.HOL
open EtaConversion RetainedNormalization HenkinTermInterpretation MathdataKernel

variable {environment : Environment} {gamma : Ctx Base} {type domain result : Ty Base}

abbrev Many {gamma : Ctx Base} {type : Ty Base} :
    Term (Constant environment) gamma type → Term (Constant environment) gamma type → Prop :=
  Relation.ReflTransGen BetaEtaStep

abbrev Positive {gamma : Ctx Base} {type : Ty Base} :
    Term (Constant environment) gamma type → Term (Constant environment) gamma type → Prop :=
  Relation.TransGen BetaEtaStep

private theorem move {other : Ctx Base} {first second : Ty Base}
    (make : Term (Constant environment) gamma first → Term (Constant environment) other second)
    (beta : ∀ {source target}, ContextualTrinity.BetaStep source target →
      ContextualTrinity.BetaStep (make source) (make target))
    (eta : ∀ {source target}, EtaStep source target → EtaStep (make source) (make target))
    {source target : Term (Constant environment) gamma first} (step : BetaEtaStep source target) :
    BetaEtaStep (make source) (make target) := by
  rcases step with reduced | step
  · obtain ⟨step⟩ := reduced
    exact Or.inl ⟨beta step⟩
  · exact Or.inr (eta step)

private theorem appFun_step (argument : Term (Constant environment) gamma domain)
    {source target : Term (Constant environment) gamma (domain ⇒ result)}
    (step : BetaEtaStep source target) : BetaEtaStep (.app source argument) (.app target argument) :=
  move (fun function => .app function argument) (fun step => .appFun argument step)
    (fun step => .appFun argument step) step

private theorem appArg_step (function : Term (Constant environment) gamma (domain ⇒ result))
    {source target : Term (Constant environment) gamma domain}
    (step : BetaEtaStep source target) : BetaEtaStep (.app function source) (.app function target) :=
  move (Term.app function) (fun step => .appArg function step) (fun step => .appArg function step) step

private theorem lam_step {source target : Term (Constant environment) (domain :: gamma) result}
    (step : BetaEtaStep source target) : BetaEtaStep (.lam source) (.lam target) :=
  move Term.lam (fun step => .lam step) (fun step => .lam step) step

private theorem all_step {source target : Formula (Constant environment) (domain :: gamma)}
    (step : BetaEtaStep source target) : BetaEtaStep (.all source) (.all target) :=
  move Term.all (fun step => .all step) (fun step => .all step) step

private theorem impLeft_step (right : Formula (Constant environment) gamma)
    {source target : Formula (Constant environment) gamma} (step : BetaEtaStep source target) :
    BetaEtaStep (.imp source right) (.imp target right) :=
  move (fun left => .imp left right) (fun step => .impLeft right step)
    (fun step => .impLeft right step) step

private theorem impRight_step (left : Formula (Constant environment) gamma)
    {source target : Formula (Constant environment) gamma} (step : BetaEtaStep source target) :
    BetaEtaStep (.imp left source) (.imp left target) :=
  move (Term.imp left) (fun step => .impRight left step) (fun step => .impRight left step) step

theorem betaHead_steps (function : Term (Constant environment) gamma (domain ⇒ result))
    (argument : Term (Constant environment) gamma domain) (stable : Bool) :
    ((betaHead function argument stable).stable = stable ∧
      (betaHead function argument stable).target = .app function argument) ∨
      Positive (.app function argument) (betaHead function argument stable).target := by
  cases function with
  | var | const | app => exact Or.inl ⟨rfl, rfl⟩
  | lam body => exact Or.inr (.single (Or.inl ⟨.beta body argument⟩))

theorem etaHead_steps (body : Term (Constant environment) (domain :: gamma) result)
    (stable : Bool) :
    ((etaHead body stable).stable = stable ∧ (etaHead body stable).target = .lam body) ∨
      Positive (.lam body) (etaHead body stable).target := by
  cases body with
  | app function argument =>
      cases argument with
      | var index =>
          cases index with
          | vz =>
              simp only [etaHead]
              split
              next lowered => exact Or.inl ⟨rfl, rfl⟩
              next target lowered =>
                  apply Or.inr
                  have same := weaken_of_rename?_drop lowered
                  change Positive (.lam (.app function (.var .vz))) target
                  rw [← same]
                  exact .single (Or.inr (.eta target))
          | vs => exact Or.inl ⟨rfl, rfl⟩
      | const | app | lam | top | bot | and | or | imp | not | eq | all | ex =>
          exact Or.inl ⟨rfl, rfl⟩
  | var | const | lam | top | bot | and | or | imp | not | eq | all | ex =>
      exact Or.inl ⟨rfl, rfl⟩

theorem normalizeOne_steps (source : Term (Constant environment) gamma type) :
    Many source (normalizeOne source).target ∧
      ((normalizeOne source).stable = false → Positive source (normalizeOne source).target) := by
  induction source with
  | var | const | top | bot | and | or | not | eq | ex =>
      exact ⟨.refl, by simp [normalizeOne, unchanged]⟩
  | app function argument ihf iha =>
      let first := normalizeOne function
      let second := normalizeOne argument
      let head := betaHead first.target second.target (first.stable && second.stable)
      change Many (.app function argument) head.target ∧
        (head.stable = false → Positive (.app function argument) head.target)
      have left : Many (.app function argument) (.app first.target argument) :=
        ihf.1.lift (fun term => Term.app term argument) (fun _ _ step => appFun_step argument step)
      have right : Many (.app first.target argument) (.app first.target second.target) :=
        iha.1.lift (Term.app first.target) (fun _ _ step => appArg_step first.target step)
      have prior := left.trans right
      rcases betaHead_steps first.target second.target (first.stable && second.stable) with
        ⟨sameStable, sameTarget⟩ | changed
      · refine ⟨?_, ?_⟩
        · change Many _ (betaHead first.target second.target _).target
          rw [sameTarget]
          exact prior
        · intro unstable
          have flags : (first.stable && second.stable) = false := sameStable.symm.trans unstable
          change Positive _ (betaHead first.target second.target _).target
          rw [sameTarget]
          rcases Bool.and_eq_false_iff.mp flags with firstBad | secondBad
          · exact ((ihf.2 firstBad).lift (fun term => Term.app term argument)
              (fun _ _ step => appFun_step argument step)).trans_left right
          · exact Relation.TransGen.trans_right left
              ((iha.2 secondBad).lift (Term.app first.target)
                (fun _ _ step => appArg_step first.target step))
      · exact ⟨prior.trans changed.to_reflTransGen,
          fun _ => Relation.TransGen.trans_right prior changed⟩
  | lam body ih =>
      let inner := normalizeOne body
      let head := etaHead inner.target inner.stable
      change Many (.lam body) head.target ∧
        (head.stable = false → Positive (.lam body) head.target)
      have prior : Many (.lam body) (.lam inner.target) :=
        ih.1.lift Term.lam (fun _ _ step => lam_step step)
      rcases etaHead_steps inner.target inner.stable with ⟨sameStable, sameTarget⟩ | changed
      · refine ⟨?_, ?_⟩
        · change Many _ (etaHead inner.target inner.stable).target
          rw [sameTarget]
          exact prior
        · intro unstable
          change Positive _ (etaHead inner.target inner.stable).target
          rw [sameTarget]
          exact (ih.2 (sameStable.symm.trans unstable)).lift Term.lam (fun _ _ step => lam_step step)
      · exact ⟨prior.trans changed.to_reflTransGen,
          fun _ => Relation.TransGen.trans_right prior changed⟩
  | imp first second ihf ihs =>
      let left := normalizeOne first
      let right := normalizeOne second
      change Many (.imp first second) (.imp left.target right.target) ∧
        ((left.stable && right.stable) = false → Positive (.imp first second) (.imp left.target right.target))
      have before : Many (.imp first second) (.imp left.target second) :=
        ihf.1.lift (fun term => Term.imp term second) (fun _ _ step => impLeft_step second step)
      have after : Many (.imp left.target second) (.imp left.target right.target) :=
        ihs.1.lift (Term.imp left.target) (fun _ _ step => impRight_step left.target step)
      refine ⟨before.trans after, ?_⟩
      intro unstable
      rcases Bool.and_eq_false_iff.mp unstable with leftBad | rightBad
      · exact ((ihf.2 leftBad).lift (fun term => Term.imp term second)
          (fun _ _ step => impLeft_step second step)).trans_left after
      · exact Relation.TransGen.trans_right before
          ((ihs.2 rightBad).lift (Term.imp left.target) (fun _ _ step => impRight_step left.target step))
  | all body ih =>
      exact ⟨ih.1.lift Term.all (fun _ _ step => all_step step),
        fun unstable => (ih.2 unstable).lift Term.all (fun _ _ step => all_step step)⟩

/-- Compute a sufficient finite budget and the exact native normal form for
every term in the typed monomorphic erasure image. Accessibility is proof
data; the computation follows the existing native pass and its stability test. -/
def complete (source : Term (Constant environment) gamma type) :
    {raw : Tm} → erase source = some raw →
      {completed : Nat × Tm // Tm.normalize completed.1 raw = some completed.2} := by
  have accessible := Mettapedia.Logic.Relation.accessible_transitiveClosure
    (BetaEtaNormalization.stronglyNormalizing source)
  induction accessible with
  | intro source _ ih =>
      intro raw erased
      obtain ⟨targetErased, sameStable⟩ := normalizeOne_erases source erased
      cases stable : (normalizeOne source).stable with
      | true =>
          refine ⟨(0, (Tm.normalizeOne raw).1), ?_⟩
          simp only [Tm.normalize]
          rw [← sameStable, stable]
          rfl
      | false =>
          have moved := Relation.TransGen.swap _ _ ((normalizeOne_steps source).2 stable)
          let rest := ih (normalizeOne source).target moved targetErased
          refine ⟨(rest.1.1 + 1, rest.1.2), ?_⟩
          simp only [Tm.normalize]
          rw [← sameStable, stable]
          exact rest.2

theorem exists_normalize (source : Term (Constant environment) gamma type)
    {raw : Tm} (erased : erase source = some raw) :
    ∃ fuel target, Tm.normalize fuel raw = some target :=
  ⟨(complete source erased).1.1, (complete source erased).1.2, (complete source erased).2⟩

/-- The full native pipeline terminates on the typed monomorphic image when
the input has no expandable declarations. The support condition is the
existing definition-normal invariant, not an assumed normalization result. -/
def completeNative (source : Term (Constant environment) gamma type)
    {raw : Tm} (erased : erase source = some raw)
    (normal : DeltaNormalInvariant.Normal environment raw) :
    {completed : Nat × Tm // MathdataKernel.normalize environment completed.1 raw = some completed.2} := by
  let result := complete source erased
  refine ⟨result.1, ?_⟩
  simp only [MathdataKernel.normalize, DeltaNormalInvariant.fixed normal]
  exact result.2

#print axioms betaHead_steps
#print axioms etaHead_steps
#print axioms normalizeOne_steps
#print axioms complete
#print axioms exists_normalize
#print axioms completeNative

end Mettapedia.Languages.Megalodon.NormalizationTermination
