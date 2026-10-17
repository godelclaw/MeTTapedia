import Mettapedia.Languages.HOLLight.KernelAtlas
import Mettapedia.Logic.HOL.ContextualTrinity
import Mettapedia.Languages.HOLLight.RetainedElaboration

/-!
# HOL Light graphs on the faces of the HOL kernel's trinity

The HOL Light proof-graph checker is a tier-0 kernel: every step is explicit,
sharing is by reference to earlier nodes, and the checker computes each step
and compares. This module places its accepted evidence on the three faces of
the contextual computational trinity of the extensional HOL calculus, at the
empty context, over the signature of the source kernel's symbols.

* **Intensional face.** Every accepted claim has a retained natural-deduction
  proof whose conclusion is the claim's translated conclusion and whose
  assumptions are among its translated hypotheses
  (`accepted_logic_element`). The proof is computed from the graph by the
  elaborator `RetainedElaboration.elaborateProved`, node by node, with each
  HOL Light rule elaborated into natural-deduction rules
  (`RetainedElaboration.elaborateProved_correct`).
* **Tier-0 certificate.** The same claim has an accepted MM0 certificate of
  polynomially bounded size, through the existing compiler.
* **Extensional face.** Its translated sequent holds in the constructed full
  model, and the retained proof's soundness gives the same reading.

`accepted_three_faces` states all three for every accepted graph, with one
polynomial. The extensional face is strictly larger than the image of the
evidence: eta holds in the full model and has no axiom-free certificate
(`extensional_beyond_evidence`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.IntensionalFloor

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.Logic.HOL.ContextualTrinity
open Mettapedia.Languages.MM0.Translation.CalculusSimulation
open Polynomial

universe w

/-- **Every accepted HOL Light claim is an element of the trinity's
intensional face**, computed by the elaborator. -/
theorem accepted_logic_element {claim : Theorem} {certificate : ProofSystem.Certificate}
    (accepted : (ProofSystem.checker emptyAxiomPolicy).check claim certificate = true) :
    ∃ φ, Translates [] claim.sequent.concl.term .prop φ ∧
      ∃ proved : ProvedSequent (Const := Symbol) [],
        proved.1.2 = φ ∧ ∀ ψ ∈ proved.1.1, ψ ∈ translatedHypotheses claim.sequent.hyp := by
  obtain ⟨proved, _, translated, hypotheses⟩ :=
    RetainedElaboration.elaborateProved_correct accepted
  exact ⟨proved.1.2, translated, proved, rfl, hypotheses⟩

/-- The retained proof's soundness in an extensional model is the semantic
reading of the translated claim. -/
theorem logic_element_sound (model : HOL.HenkinModel.{0, 0, w} AtomicTy Symbol)
    (respects : model.FunctionsRespectEqv) (proved : ProvedSequent (Const := Symbol) [])
    (hypothesesHold : ∀ ψ ∈ proved.1.1, model.models ψ) : model.models proved.1.2 :=
  HOL.Soundness.extDerivation_sound proved.2.erase respects (fun index => nomatch index)
    (fun ψ member => hypothesesHold ψ member)

/-- **Accepted HOL Light evidence on all three faces, with its tier-0 MM0
certificate.** -/
theorem accepted_three_faces :
    ∃ polynomial : ℕ[X], ∀ (claim : Theorem) (graph : ProofSystem.Certificate),
      (ProofSystem.checker emptyAxiomPolicy).check claim graph = true →
        ((savedChecker FirstOrder.Kernel.firstOrder).check (FirstOrder.render claim)
            (FirstOrder.Kernel.mm0Simulation.translate claim graph) = true ∧
          (savedChecker FirstOrder.Kernel.firstOrder).certificateSize
              (FirstOrder.Kernel.mm0Simulation.translate claim graph) ≤
            polynomial.eval ((FirstOrder.holChecker emptyAxiomPolicy
              FirstOrder.Kernel.firstOrder).inputSize (claim, graph))) ∧
        (∃ φ, Translates [] claim.sequent.concl.term .prop φ ∧
          ∃ proved : ProvedSequent (Const := Symbol) [],
            proved.1.2 = φ ∧ ∀ ψ ∈ proved.1.1, ψ ∈ translatedHypotheses claim.sequent.hyp) ∧
        KernelAtlas.StandardMeaning.{w} claim := by
  obtain ⟨polynomial, bounded⟩ := FirstOrder.Kernel.mm0Simulation.sizeBound
  refine ⟨polynomial, fun claim graph accepted => ⟨⟨?_, ?_⟩, accepted_logic_element accepted,
    KernelAtlas.checked_standard_meaning accepted⟩⟩
  · exact FirstOrder.Kernel.mm0Simulation.preserves claim graph accepted
  · exact bounded (claim, graph)

/-- **The extensional face is strictly larger than the evidence.** Eta holds
in the full model, and the axiom-free MM0 hosting has no certificate for it. -/
theorem extensional_beyond_evidence (name : Name) (domain codomain : Ty) :
    ∃ φ, Translates [] (Eta.equation name domain codomain).term .prop φ ∧
      ModelInterpretation.Controls.initialModel.{w}.models φ ∧
      ∀ certificate : SavedCertificate,
        (savedChecker FirstOrder.Kernel.firstOrder).check
          (FirstOrder.renderSequent ⟨∅, Eta.equation name domain codomain⟩) certificate = false :=
  KernelAtlas.eta_true_without_axiom_free_certificate name domain codomain

#print axioms accepted_logic_element
#print axioms accepted_three_faces

end Mettapedia.Languages.HOLLight.IntensionalFloor
