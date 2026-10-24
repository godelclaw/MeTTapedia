import Mettapedia.Languages.HOLLight.RetainedCompilation
import Mettapedia.Languages.HOLLight.FirstOrder.GraphSimulation
import Mettapedia.Languages.HOLLight.FirstOrder.Validation

/-!
# Retained HOL proofs in the generated MM0 HOL-rule theory

The all-constructor HOL compiler first builds an actual HOL Light primitive
graph. The existing structural graph compiler then builds MM0 saved-proof
witnesses for the first-order presentation of that kernel, with the eta axiom
listed explicitly. The result preserves the exact rendered sequent and is
checked by `MM0.Kernel.ProofWitness.check` through the saved-proof interface.

This theory encodes HOL terms and rule operations as first-order data. It is
distinct from the maintained `hol.mm0` syntax and theorem inventory. No
identification with that presentation, proof-identity bijection, or native
binary qualification is asserted by this composition.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.RetainedMM0Compilation

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.MM0.Translation.CalculusSimulation
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker

instance : DecidablePred etaAxiomPolicy := fun claim =>
  (inferInstance : Decidable (claim = EtaAxiom.sequent))

def axioms : List Sequent := [EtaAxiom.sequent]
def calculus : ValidatedCalculusLanguageDef := FirstOrder.validatedHolCalculus axioms

theorem firstOrder : FirstOrderCalculus calculus.1 := FirstOrder.holCalculus_firstOrder_axioms axioms

theorem inList : ∀ sequent, etaAxiomPolicy sequent → sequent ∈ axioms := by
  rintro sequent rfl
  exact List.mem_singleton_self _

theorem admitted : ∀ sequent ∈ axioms, sequent.hyp = ∅ ∧ etaAxiomPolicy sequent ∧ sequent.IsBool := by
  intro sequent member
  have same : sequent = EtaAxiom.sequent := by simpa [axioms] using member
  subst sequent
  exact ⟨rfl, rfl, EtaAxiom.sequent_isBool⟩

/-- This is the pre-existing structural graph-to-MM0 algorithm, instantiated
at the actual finite HOL-rule presentation and its explicit eta policy. -/
def simulation := FirstOrder.mm0Simulation (axioms := axioms) (definition := calculus) rfl inList firstOrder

def compile {Γ : HOL.Ctx AtomicTy} {Δ : List (HOL.Formula Symbol Γ)} {φ : HOL.Formula Symbol Γ}
    (proof : HOL.ProofSyntax Symbol Δ φ) (names : ReverseTranslation.Naming Γ) (origin : ProofExecution.Origin) :
    SavedCertificate :=
  let native := (RetainedCompilation.compile etaAxiomPolicy rfl proof names origin).proof
  simulation.translate native.result native.certificate

theorem compile_accepted {Γ : HOL.Ctx AtomicTy} {Δ : List (HOL.Formula Symbol Γ)} {φ : HOL.Formula Symbol Γ}
    (proof : HOL.ProofSyntax Symbol Δ φ) (names : ReverseTranslation.Naming Γ) (origin : ProofExecution.Origin) :
    (savedChecker firstOrder).check
      (FirstOrder.renderSequent
        ⟨ReverseTranslation.reverseHypotheses names (Δ.map HOL.ImpredicativeConnectives.expand),
         ReverseTranslation.reverseCanonical names (HOL.ImpredicativeConnectives.expand φ)⟩)
      (compile proof names origin) = true := by
  let native := RetainedCompilation.compile etaAxiomPolicy rfl proof names origin
  have accepted := simulation.preserves native.proof.result native.proof.certificate native.proof.accepted
  have sequent : native.proof.result.sequent =
      ⟨ReverseTranslation.reverseHypotheses names (Δ.map HOL.ImpredicativeConnectives.expand),
       ReverseTranslation.reverseCanonical names (HOL.ImpredicativeConnectives.expand φ)⟩ :=
    Sequent.ext native.hypotheses_exact native.conclusion_exact
  have rendered : FirstOrder.render native.proof.result = FirstOrder.renderSequent
      ⟨ReverseTranslation.reverseHypotheses names (Δ.map HOL.ImpredicativeConnectives.expand),
       ReverseTranslation.reverseCanonical names (HOL.ImpredicativeConnectives.expand φ)⟩ := by
    apply Subtype.ext
    simp only [FirstOrder.render, FirstOrder.renderSequent, sequent]
  simpa only [comapChecker, rendered, compile, native] using accepted

/-- On this particular theory, acceptance of a sequent has the full HOL Light
source-derivation converse, without reconstructing the original proof identity. -/
theorem accepted_sequent_iff (sequent : Sequent) :
    (∃ certificate, (savedChecker firstOrder).check (FirstOrder.renderSequent sequent) certificate = true) ↔
      ∃ out : Theorem, Derives (Rule etaAxiomPolicy) out ∧ out.sequent = sequent :=
  FirstOrder.savedChecker_exact (axioms := axioms) (definition := calculus) rfl
    admitted inList firstOrder sequent

end Mettapedia.Languages.HOLLight.RetainedMM0Compilation
