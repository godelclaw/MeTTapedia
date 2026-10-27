import Mettapedia.Logic.HOL.Semantics.KripkeHenkinGeneral
import Mettapedia.Logic.HOL.ProofSyntaxModulo

/-!
# Proofs modulo conversion in Kripke–Henkin general models

A Kripke–Henkin general model quantifies over the admissible values at each world and reads equality as an equality
that may grow along the worlds; its admissible functions respect it. The constant-domain Kripke models of
`ProofSyntaxModuloKripke` are the case where every function is admissible and equality is identity.

Every proof modulo the defining equations is sound in every such model where the equations hold
(`proofSyntaxModulo_sound`): at every world and admissible valuation where the hypotheses hold, the conclusion holds.
A conversion step keeps the denotation (`sourceStep_denote`), and instantiating a universal quantifier uses that every
term denotes an admissible value (`term_closed`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.KripkeHenkinGeneral

universe u v x

variable {Base : Type u} {Const : Ty Base → Type v} (M : KripkeHenkinGeneral.{u, v, x} Base Const)

/-- The defining equations hold: both sides denote the same value at every valuation of the pattern telescope. -/
def EquationsHold (equations : List (DefiningEquation Const)) : Prop :=
  ∀ equation ∈ equations, ∀ ρ : M.Valuation equation.context,
    M.denote equation.left ρ = M.denote equation.right ρ

theorem sourceStep_denote {equations : List (DefiningEquation Const)} (hold : M.EquationsHold equations)
    {Γ : Ctx Base} {τ : Ty Base} {s t : Term Const Γ τ} (step : SourceStep equations s t) :
    ∀ ρ : M.Valuation Γ, M.denote s ρ = M.denote t ρ := by
  induction step with
  | beta body argument =>
      intro ρ
      exact (M.toKripkePreModel.denote_instantiate argument body ρ).symm
  | delta equation listed substitution _ =>
      intro ρ
      show M.toKripkePreModel.denote _ ρ = M.toKripkePreModel.denote _ ρ
      rw [M.toKripkePreModel.denote_subst, M.toKripkePreModel.denote_subst]
      exact hold equation listed _
  | appFun argument _ ih => intro ρ; exact congrFun (ih ρ) _
  | appArg function _ ih => intro ρ; exact congrArg (M.denote function ρ) (ih ρ)
  | lam _ ih => intro ρ; funext d; exact ih _
  | impLeft right _ ih =>
      intro ρ
      show M.toKripkePreModel.denote _ ρ = M.toKripkePreModel.denote _ ρ
      simp only [KripkePreModel.denote]
      rw [show M.toKripkePreModel.denote _ ρ = _ from ih ρ]
  | impRight left _ ih =>
      intro ρ
      show M.toKripkePreModel.denote _ ρ = M.toKripkePreModel.denote _ ρ
      simp only [KripkePreModel.denote]
      rw [show M.toKripkePreModel.denote _ ρ = _ from ih ρ]
  | eqLeft right _ ih =>
      intro ρ
      show M.toKripkePreModel.denote _ ρ = M.toKripkePreModel.denote _ ρ
      simp only [KripkePreModel.denote]
      rw [show M.toKripkePreModel.denote _ ρ = _ from ih ρ]
  | eqRight left _ ih =>
      intro ρ
      show M.toKripkePreModel.denote _ ρ = M.toKripkePreModel.denote _ ρ
      simp only [KripkePreModel.denote]
      rw [show M.toKripkePreModel.denote _ ρ = _ from ih ρ]
  | all _ ih =>
      intro ρ
      show M.toKripkePreModel.denote _ ρ = M.toKripkePreModel.denote _ ρ
      simp only [KripkePreModel.denote]
      funext W
      refine propext (forall_congr' fun V => imp_congr_right fun _ => forall_congr' fun d =>
        imp_congr_right fun _ => ?_)
      rw [show M.toKripkePreModel.denote _ _ = _ from ih _]

theorem coreConversion_denote {equations : List (DefiningEquation Const)} (hold : M.EquationsHold equations)
    {Γ : Ctx Base} {τ : Ty Base} {s t : Term Const Γ τ} (conversion : CoreConversion equations s t)
    (ρ : M.Valuation Γ) : M.denote s ρ = M.denote t ρ := by
  induction conversion with
  | rel _ _ step => exact M.sourceStep_denote hold step.2.2 ρ
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ first second => exact first.trans second

/-- **Soundness.** At every world and admissible valuation where the hypotheses hold, the conclusion of a proof
modulo the equations holds, in every Kripke–Henkin general model of the equations. -/
theorem proofSyntaxModulo_sound {equations : List (DefiningEquation Const)} (hold : M.EquationsHold equations)
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ}
    (proof : ProofSyntaxModulo equations Δ φ) :
    ∀ (ρ : M.Valuation Γ) (W : M.World), M.ValuationAdm W ρ → M.DenotesHyps W ρ Δ → M.denote φ ρ W := by
  induction proof with
  | hyp occurrence => exact fun ρ W _ hyps => hyps _ (List.get_mem _ occurrence)
  | impI _ ih =>
      intro ρ W admissible hyps V later premise
      exact ih ρ V (M.toKripkePreModel.valuationAdm_mono later admissible)
        (M.denotesHyps_cons premise (M.denotesHyps_mono admissible later hyps))
  | impE _ _ ihf iha =>
      intro ρ W admissible hyps
      exact ihf ρ W admissible hyps W (M.le_refl W) (iha ρ W admissible hyps)
  | allI _ ih =>
      intro ρ W admissible hyps V later d hd
      exact ih (M.extend ρ d) V
        (M.toKripkePreModel.extend_adm (M.toKripkePreModel.valuationAdm_mono later admissible) hd)
        (M.denotesHyps_weaken_extend (M.denotesHyps_mono admissible later hyps) d)
  | allE term _ ih =>
      intro ρ W admissible hyps
      exact Eq.mpr (congrFun (M.toKripkePreModel.denote_instantiate term _ ρ) W)
        (ih ρ W admissible hyps W (M.le_refl W) _ (M.term_closed term W ρ admissible))
  | convert conversion _ ih =>
      intro ρ W admissible hyps
      rw [← M.coreConversion_denote hold conversion ρ]
      exact ih ρ W admissible hyps

/-- **Closed proofs**: a closed proof from hypotheses that hold at a world proves a formula holding there. -/
theorem proofSyntaxModulo_sound_closed {equations : List (DefiningEquation Const)} (hold : M.EquationsHold equations)
    {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const} (proof : ProofSyntaxModulo equations Δ φ)
    (W : M.World) (hyps : ∀ δ ∈ Δ, M.denote δ M.emptyVal W) : M.denote φ M.emptyVal W :=
  M.proofSyntaxModulo_sound hold proof M.emptyVal W (M.emptyVal_adm W) hyps

end Mettapedia.Logic.HOL.KripkeHenkinGeneral
