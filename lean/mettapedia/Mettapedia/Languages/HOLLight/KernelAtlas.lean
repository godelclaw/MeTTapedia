import Mettapedia.Languages.HOLLight.MM0Meaning
import Mettapedia.Languages.HOLLight.CheckingDiscipline
import Mettapedia.GSLT.LanguageDef.HeuristicEvidence
import Mettapedia.Languages.HOLLight.IncrementalExecution
import Mettapedia.Machines.ProductiveCoreAdapters
import Mettapedia.GSLT.Distinction.SimulationComposition

/-!
# HOL Light in the kernel atlas

The actual graph checker, the existing HOL-to-MM0 certificate compiler and the
constructed full-domain model meet here. A suggested proof is first checked;
its compiled MM0 certificate then has both original-checker acceptance and
the established polynomial certificate-size bound. This module supplies no
executed translator clock. The old `PSimulation` time field is a declared
account and cannot supply one.

The configured axiom-free kernel is deliberately kept distinct from the
model's standard commitments. In that configuration eta is model-valid yet
unprovable; adding ETA as an axiom changes the presentation. Hosting exactness
therefore does not mean completeness for the chosen models.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.KernelAtlas

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.MM0.Translation.CalculusSimulation
open Polynomial

universe w

def StandardMeaning (claim : Theorem) : Prop :=
  ∃ φ, Translates [] claim.sequent.concl.term .prop φ ∧
    ((∀ ψ ∈ translatedHypotheses claim.sequent.hyp,
      ModelInterpretation.Controls.initialModel.{w}.models ψ) →
      ModelInterpretation.Controls.initialModel.{w}.models φ)

/-- Direct HOL graph acceptance is sound in the constructed full model. -/
theorem checked_standard_meaning {claim : Theorem} {graph : ProofSystem.Certificate}
    (accepted : (ProofSystem.checker emptyAxiomPolicy).check claim graph = true) :
    StandardMeaning.{w} claim :=
  ProofSystem.checker_models accepted ModelInterpretation.Controls.initialModel
    (HOL.HenkinModel.functionsRespectEqv_of_fullDomains _
      ModelInterpretation.Controls.initialModel_fullDomains)

/-- The model's infinite individual carrier is the ordinary natural numbers,
up to the universe lift. Full domains include every function on it. -/
noncomputable def individualEquivNat :
    ModelInterpretation.Controls.initialModel.{w}.Carrier
      TypeFamilySemantics.Controls.individual ≃ Nat :=
  TypeFamilySemantics.Controls.individualValueEquiv.trans Equiv.ulift

/-- One polynomial works for every submitted graph in this fixed source
configuration. The bound concerns the existing structural certificate measure,
not the time needed to construct or check the compiled certificate. -/
theorem screened_graph_bounded_mm0_replay :
    ∃ polynomial : ℕ[X], ∀ (claim : Theorem) (proposals : List ProofSystem.Certificate)
      (graph : ProofSystem.Certificate),
      graph ∈ HeuristicEvidence.screen (ProofSystem.checker emptyAxiomPolicy) claim proposals →
      let certificate := FirstOrder.Kernel.mm0Simulation.translate claim graph
      (savedChecker FirstOrder.Kernel.firstOrder).check (FirstOrder.render claim) certificate = true ∧
      (savedChecker FirstOrder.Kernel.firstOrder).certificateSize certificate ≤
        polynomial.eval ((FirstOrder.holChecker emptyAxiomPolicy
          FirstOrder.Kernel.firstOrder).inputSize (claim, graph)) ∧
      StandardMeaning.{w} claim := by
  obtain ⟨polynomial, bounded⟩ := FirstOrder.Kernel.mm0Simulation.sizeBound
  refine ⟨polynomial, ?_⟩
  intro claim proposals graph selected
  have checked := (HeuristicEvidence.mem_screen _ _ _ _).mp selected |>.2
  exact ⟨FirstOrder.Kernel.mm0Simulation.preserves claim graph checked,
    bounded (claim, graph), checked_standard_meaning checked⟩

/-- Changing how certificates are proposed changes no acceptance authority. -/
theorem arbitrary_producer_standard_sound (producer : Theorem → List ProofSystem.Certificate)
    (claim : Theorem) (graph : ProofSystem.Certificate)
    (selected : graph ∈ HeuristicEvidence.screen (ProofSystem.checker emptyAxiomPolicy)
      claim (producer claim)) : StandardMeaning.{w} claim :=
  checked_standard_meaning ((HeuristicEvidence.mem_screen _ _ _ _).mp selected).2

/-- A concrete truth/proof gap: eta holds in this full model, while the
axiom-free HOL configuration and its exact MM0 hosting have no certificate. -/
theorem eta_true_without_axiom_free_certificate (name : Name) (domain codomain : Ty) :
    ∃ φ, Translates [] (Eta.equation name domain codomain).term .prop φ ∧
      ModelInterpretation.Controls.initialModel.{w}.models φ ∧
      ∀ certificate : SavedCertificate,
        (savedChecker FirstOrder.Kernel.firstOrder).check
          (FirstOrder.renderSequent ⟨∅, Eta.equation name domain codomain⟩) certificate = false := by
  obtain ⟨φ, translated, trueInModels, refused⟩ :=
    MM0Meaning.Controls.eta_models_without_kernel_certificate name domain codomain
  exact ⟨φ, translated, trueInModels _
    (HOL.HenkinModel.functionsRespectEqv_of_fullDomains _
      ModelInterpretation.Controls.initialModel_fullDomains), refused⟩

namespace Controls

theorem submitted_reflexivity_retained :
    HeuristicEvidence.screen (ProofSystem.checker emptyAxiomPolicy)
      ProofExecution.Controls.reflexivityTheorem [ProofSystem.Controls.reflexivityCertificate] =
        [ProofSystem.Controls.reflexivityCertificate] := by
  simp [HeuristicEvidence.screen, ProofSystem.Controls.reflexivity_accepted]

theorem wrong_root_discarded :
    HeuristicEvidence.screen (ProofSystem.checker emptyAxiomPolicy)
      ProofExecution.Controls.reflexivityTheorem
      [([ProofExecution.Controls.reflexivity ("authored", 0)], 1)] = [] := by
  simp [HeuristicEvidence.screen, ProofSystem.Controls.reflexivity_wrong_root]

end Controls

end Mettapedia.Languages.HOLLight.KernelAtlas

namespace Mettapedia.Languages.HOLLight.ExportCodec

open Mettapedia.Machines
open Mettapedia.Machines.ProductiveCoreAdapters
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open Mettapedia.Languages.OpenTheory Lean

def EventWork.settled (work : EventWork) : Bool := work.rejected || work.remaining.isEmpty

theorem EventWork.settled_iff (work : EventWork) : work.settled = true ↔ work.Settled := by
  simp [EventWork.settled, EventWork.Settled]

/-- One transition receives one original source event. A terminal report
retains the complete accepted theory/proof state and any refused suffix. -/
def checkingCore (policy : AxiomPolicy) [DecidablePred policy] :
    AnswerMachineCore (State × List Json) EventWork where
  State := EventWork
  load input := eventWork input.1 input.2
  step work := if work.settled then none else some (tickWork policy work)
  answer work := if work.settled then some work else none
  answer_final := by intro work result; split <;> simp_all

theorem checkingCore_retainedTick (policy : AxiomPolicy) [DecidablePred policy] :
    retainedTick (checkingCore policy).toMachineCore = tickWork policy := by
  funext work
  cases settled : work.settled with
  | false => simp [retainedTick, checkingCore, settled]; rfl
  | true =>
      simp [retainedTick, checkingCore, settled,
        tickWork_settled policy work ((EventWork.settled_iff work).mp settled)]
      rfl

def checkingObject (policy : AxiomPolicy) [DecidablePred policy] :
    ObservedMachine (Occurrence EventWork) EventWork Empty :=
  ObservedMachine.of (answerMachine (checkingCore policy))

/-- The existing finite source-event bound becomes an actual terminating
run in the machine category. Event count is separate from each event's local
typing, substitution, parsing and inference costs. -/
theorem checkingObject_completes (policy : AxiomPolicy) [DecidablePred policy] (work : EventWork) :
    ∃ fuel events report, fuel ≤ work.remaining.length + 1 ∧
      (checkingObject policy).machine.run fuel work = (events, .finished report) ∧
      report = advanceWork policy work.remaining.length work ∧
      report.meaning policy = work.meaning policy := by
  let final := advanceWork policy work.remaining.length work
  have settled : final.settled = true := (EventWork.settled_iff _).mpr (advanceWork_finishes policy work)
  have observed : (checkingCore policy).answer final = some final := by simp [checkingCore, settled]
  have ticks : (retainedTick (checkingCore policy).toMachineCore)^[work.remaining.length] work = final := by
    rw [checkingCore_retainedTick]
    rfl
  obtain ⟨fuel, events, count, finished⟩ := retainedTick_finished (checkingCore policy)
    work.remaining.length work final (by simpa [ticks] using observed)
  exact ⟨fuel, events, final, count, finished, rfl, advanceWork_meaning policy _ work⟩

end Mettapedia.Languages.HOLLight.ExportCodec
