import Mettapedia.OSLF.NativeTypes.GeneratedLogic.RhoPartnerAdequacy

/-!
# Controls: plain steps do not tell a waiting receiver from the inert process, and a partner does

`for(y<-@0){0}` waits on the channel `@0`; `0` is inert. Neither takes a plain step, so the front door's plain forward
formulas do not tell them apart (`plain_agree`). Beside the output `@0!(0)` the receiver communicates and the inert
process does not, so the partner's formula `⟨{x, @0!(0)}⟩⊤` holds at one and fails at the other
(`partnerFormula_separates`), and the two have different native types under parallel partners (`partners_separate`).
This is the front door's reading of `ParallelContextAdequacy.reduction_bisimilarity_not_partner_adequate`.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.Rho.Partners

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT (RhoProcess rhoLanguageDefGSLT closedCommSource_step)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem (closedNil closedCommTarget)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.ParallelContextAdequacy (waitingInput outputPartner partner_step
  no_step_of_successors_nil waitingInput_successors closedNil_successors nilPartner_successors
  waitingInput_not_partner_bisimilar_nil)

/-- A plain step from a closed process reaches a closed process. -/
theorem process_of_step_any {source target : Pattern} (sourceIn : process source = true)
    (step : frontDoor.step source .any target) : process target = true := by
  obtain ⟨-, -, redex, contractum, witness, before, -, valid, -, after, -⟩ := step
  exact process_invariant (process_of_step (process_invariant sourceIn before) valid.2) after

/-- A closed process with no canonical successor takes no plain step at the front door. -/
theorem no_plain_step {source : RhoProcess}
    (none : Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep.rewriteAt
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep.rhoRuleInterpretation
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep.rhoBasePremises rhoCalc 1
      (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical.canonicalize source.1) = [])
    (target : Pattern) : ¬ frontDoor.step source.1 .any target := by
  intro step
  have targetIn := process_of_step_any (process_closed source) step
  exact no_step_of_successors_nil none (ofProcess targetIn) ((step_any_iff source (ofProcess targetIn)).mp step)

/-- The plain step label. -/
def plainLabel (label : StepLabel) : Bool := label == .any

/-- **Plain forward formulas do not tell the waiting receiver from the inert process**: neither steps. -/
theorem plain_agree : frontDoor.AgreeOn (Formula.forwardOn plainLabel) waitingInput.1 closedNil.1 := by
  refine NativeStructure.agree_of_forwardBisimilar ⟨fun first second => first = waitingInput.1 ∧ second = closedNil.1,
    ⟨?_, ?_⟩, rfl, rfl⟩
  · rintro _ _ label next ⟨rfl, rfl⟩ plain step
    obtain rfl : label = .any := by simpa [plainLabel] using plain
    exact (no_plain_step waitingInput_successors next step).elim
  · rintro _ _ label next ⟨rfl, rfl⟩ plain step
    obtain rfl : label = .any := by simpa [plainLabel] using plain
    exact (no_plain_step closedNil_successors next step).elim

/-- **The output partner's formula holds at the receiver and fails at the inert process.** -/
theorem partnerFormula_separates :
    frontDoor.sat Env.closed (.possibly (partnerLabel outputPartner) .top) waitingInput.1 ∧
      ¬ frontDoor.sat Env.closed (.possibly (partnerLabel outputPartner) .top) closedNil.1 := by
  constructor
  · exact ⟨closedCommTarget.1, (step_partner_iff outputPartner waitingInput closedCommTarget).mpr partner_step, trivial⟩
  · rintro ⟨target, step, -⟩
    have targetIn := closedUnder (process_closed closedNil) (isPartnerLabel_partnerLabel outputPartner) step
    exact no_step_of_successors_nil nilPartner_successors (ofProcess targetIn)
      ((step_partner_iff outputPartner closedNil (ofProcess targetIn)).mp step)

/-- **Under parallel partners the two have different native types.** -/
theorem partners_separate : ¬ frontDoor.AgreeOn (Formula.forwardOn isPartnerLabel) waitingInput.1 closedNil.1 :=
  fun agree => waitingInput_not_partner_bisimilar_nil ((agree_iff_partnerBisimilar waitingInput closedNil).mp agree)

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.Rho.Partners
