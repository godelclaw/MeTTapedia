import Mettapedia.Languages.HOLLight.FirstOrder.GraphSimulation
import Mettapedia.Languages.HOLLight.FirstOrder.Validation
import Mettapedia.Languages.HOLLight.ModelInterpretation
import Mettapedia.Languages.OpenTheory.ReachabilitySemantics

/-!
# MM0 acceptance and the meaning of configured HOL Light sequents

The existing graph rendering and saved-proof checker host a fixed finite HOL
Light axiom configuration. Successful MM0 checking is equivalent to HOL Light
derivability of the original sequent, and to the existing proof-building GSLT's
reachability observation. These are existence laws; they supply no efficient
arbitrary reverse-certificate extraction.

Semantic soundness uses the original extensional Henkin interpretation. A
configured axiom must be provable from a background theory that is closed under
source substitutions and contains no free-variable symbols. Merely satisfying
one finite axiom instance is insufficient when `INST` or `INST_TYPE` can use it
as a schema. Definitions that are rendered as finite axioms retain this same
explicit semantic obligation; conservativity is not inferred.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MM0Meaning

open Mettapedia.Languages.OpenTheory Mettapedia.Logic
open Mettapedia.Languages.MM0.Translation.CalculusSimulation
open Mettapedia.GSLT.LanguageDef (ValidatedCalculusLanguageDef)
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

universe w

section Configured

variable {axioms : List Sequent} {definition : ValidatedCalculusLanguageDef}
  (calculus : definition.1 = FirstOrder.holCalculus axioms)
  {policy : AxiomPolicy} [DecidablePred policy]
  (admitted : ∀ sequent ∈ axioms,
    sequent.hyp = ∅ ∧ policy sequent ∧ sequent.IsBool)
  (inList : ∀ sequent, policy sequent → sequent ∈ axioms)
  (firstOrder : FirstOrderCalculus definition.1)

include calculus admitted inList

/-- The same configured acceptance is exactly the existing source GSLT's
finite proof-building reachability, with the original stored theorem witness. -/
theorem accepted_iff_reachable (sequent : Sequent) :
    (∃ certificate, (savedChecker firstOrder).check
      (FirstOrder.renderSequent sequent) certificate = true) ↔
    ∃ (out : Theorem) (state : ProofExecution.State),
      (ProofExecution.gslt policy).MultiStep ProofExecution.empty state ∧
      out ∈ state.cache ∧ out.sequent = sequent := by
  rw [FirstOrder.savedChecker_exact calculus admitted inList firstOrder sequent]
  constructor
  · rintro ⟨out, derived, same⟩
    obtain ⟨state, path, present⟩ :=
      (ProofExecution.derives_iff_reachable policy out).mp derived
    exact ⟨out, state, path, present, same⟩
  · rintro ⟨out, state, path, present, same⟩
    exact ⟨out, (ProofExecution.derives_iff_reachable policy out).mpr
      ⟨state, path, present⟩, same⟩

/-- Acceptance agrees with the original generated native type at its
reachability-scale observation. This forgets no theorem witness. -/
theorem accepted_iff_nativeType (sequent : Sequent) :
    (∃ certificate, (savedChecker firstOrder).check
      (FirstOrder.renderSequent sequent) certificate = true) ↔
    ∃ out : Theorem, out.sequent = sequent ∧
      (gsltOSLF (ProofExecution.gslt policy).closure).satisfies (S := ())
        ProofExecution.empty (ProofExecution.theoremNativeType policy out).pred := by
  rw [FirstOrder.savedChecker_exact calculus admitted inList firstOrder sequent]
  constructor
  · rintro ⟨out, derived, same⟩
    exact ⟨out, same,
      (ProofExecution.satisfies_theoremNativeType_iff policy out).mpr derived⟩
  · rintro ⟨out, same, observed⟩
    exact ⟨out,
      (ProofExecution.satisfies_theoremNativeType_iff policy out).mp observed, same⟩

/-- A successful MM0 certificate has the original HOL meaning in every
extensional Henkin model of the configured substitution-closed background. -/
theorem accepted_models {Θ : HOL.ClosedTheorySet Symbol}
    (background : VariableFreeSubstitutionClosed Θ)
    (axiomsProvable : ∀ sequent ∈ axioms, TranslatedProvable Θ sequent)
    {sequent : Sequent} {certificate : SavedCertificate}
    (accepted : (savedChecker firstOrder).check
      (FirstOrder.renderSequent sequent) certificate = true)
    (model : HOL.HenkinModel.{0, 0, w} AtomicTy Symbol)
    (extensional : model.FunctionsRespectEqv)
    (backgroundHolds : ∀ ψ ∈ Θ, model.models ψ) :
    ∃ φ, Translates [] sequent.concl.term .prop φ ∧
      ((∀ ψ ∈ translatedHypotheses sequent.hyp, model.models ψ) → model.models φ) := by
  obtain ⟨out, derived, same⟩ :=
    (FirstOrder.savedChecker_exact calculus admitted inList firstOrder sequent).mp
      ⟨certificate, accepted⟩
  have shared := derives_shared policy derived
  have authorized := derives_only_authorized_axioms policy shared
  obtain ⟨φ, translated, sound⟩ := derives_models background shared
    (fun tagged member => axiomsProvable tagged (inList tagged (authorized tagged member)))
    model extensional backgroundHolds
  rw [same] at translated sound
  exact ⟨φ, translated, sound⟩

/-- A supplied independent translation fixes the conclusion formula. This
states model truth directly, rather than truth of an encoded proof predicate. -/
theorem accepted_models_of_translation {Θ : HOL.ClosedTheorySet Symbol}
    (background : VariableFreeSubstitutionClosed Θ)
    (axiomsProvable : ∀ sequent ∈ axioms, TranslatedProvable Θ sequent)
    {sequent : Sequent} {certificate : SavedCertificate}
    (accepted : (savedChecker firstOrder).check
      (FirstOrder.renderSequent sequent) certificate = true)
    {φ : HOL.ClosedFormula Symbol}
    (translation : Translates [] sequent.concl.term .prop φ)
    (model : HOL.HenkinModel.{0, 0, w} AtomicTy Symbol)
    (extensional : model.FunctionsRespectEqv)
    (backgroundHolds : ∀ ψ ∈ Θ, model.models ψ)
    (hypothesesHold : ∀ ψ ∈ translatedHypotheses sequent.hyp, model.models ψ) :
    model.models φ := by
  obtain ⟨actual, translated, sound⟩ := accepted_models calculus admitted inList firstOrder
    background axiomsProvable accepted model extensional backgroundHolds
  have same := Translates.unique_eq translated translation
  cases same
  exact sound hypothesesHold

/-- A falsifying applicable model rules out every MM0 saved-proof certificate
for the independently translated sequent. Incompleteness of execution is not
used as a negative proof witness. -/
theorem refused_of_countermodel {Θ : HOL.ClosedTheorySet Symbol}
    (background : VariableFreeSubstitutionClosed Θ)
    (axiomsProvable : ∀ sequent ∈ axioms, TranslatedProvable Θ sequent)
    (sequent : Sequent) {φ : HOL.ClosedFormula Symbol}
    (translation : Translates [] sequent.concl.term .prop φ)
    (model : HOL.HenkinModel.{0, 0, w} AtomicTy Symbol)
    (extensional : model.FunctionsRespectEqv)
    (backgroundHolds : ∀ ψ ∈ Θ, model.models ψ)
    (hypothesesHold : ∀ ψ ∈ translatedHypotheses sequent.hyp, model.models ψ)
    (falseConclusion : ¬ model.models φ) (certificate : SavedCertificate) :
    (savedChecker firstOrder).check (FirstOrder.renderSequent sequent) certificate = false := by
  rw [Bool.eq_false_iff]
  intro accepted
  exact falseConclusion (accepted_models_of_translation calculus admitted inList firstOrder
    background axiomsProvable accepted translation model extensional
    backgroundHolds hypothesesHold)

/-- The actual graph translator's emitted MM0 certificate has the original
conclusion's model meaning. The supplied graph is checked by the original HOL
kernel; the target certificate is the existing chronological translation. -/
theorem translated_graph_models {Θ : HOL.ClosedTheorySet Symbol}
    (background : VariableFreeSubstitutionClosed Θ)
    (axiomsProvable : ∀ sequent ∈ axioms, TranslatedProvable Θ sequent)
    {claim : Theorem} {graph : ProofSystem.Certificate}
    (checked : (ProofSystem.checker policy).check claim graph = true)
    (model : HOL.HenkinModel.{0, 0, w} AtomicTy Symbol)
    (extensional : model.FunctionsRespectEqv)
    (backgroundHolds : ∀ ψ ∈ Θ, model.models ψ) :
    (savedChecker firstOrder).check (FirstOrder.render claim)
      ((FirstOrder.mm0Simulation calculus inList firstOrder).translate claim graph) = true ∧
    ∃ φ, Translates [] claim.sequent.concl.term .prop φ ∧
      ((∀ ψ ∈ translatedHypotheses claim.sequent.hyp, model.models ψ) → model.models φ) := by
  have accepted := (FirstOrder.mm0Simulation calculus inList firstOrder).preserves
    claim graph checked
  have targetAccepted : (savedChecker firstOrder).check
      (FirstOrder.renderSequent claim.sequent)
      ((FirstOrder.mm0Simulation calculus inList firstOrder).translate claim graph) = true :=
    accepted
  exact ⟨accepted, accepted_models calculus admitted inList firstOrder background
    axiomsProvable targetAccepted model extensional backgroundHolds⟩

end Configured

section Kernel

/-- The axiom-free saved MM0 checker implies HOL truth in every extensional
Henkin model, with only the original sequent's hypotheses as assumptions. -/
theorem kernel_models {sequent : Sequent} {certificate : SavedCertificate}
    (accepted : (savedChecker FirstOrder.Kernel.firstOrder).check
      (FirstOrder.renderSequent sequent) certificate = true)
    (model : HOL.HenkinModel.{0, 0, w} AtomicTy Symbol)
    (extensional : model.FunctionsRespectEqv) :
    ∃ φ, Translates [] sequent.concl.term .prop φ ∧
      ((∀ ψ ∈ translatedHypotheses sequent.hyp, model.models ψ) → model.models φ) := by
  exact accepted_models (axioms := [])
    (definition := FirstOrder.CalculusControls.validated) rfl
    (policy := emptyAxiomPolicy) (fun _ member => by cases member)
    (fun _ impossible => impossible.elim) FirstOrder.Kernel.firstOrder
    variableFreeSubstitutionClosed_empty (fun _ member => by cases member)
    accepted model extensional (fun _ member => absurd member (Set.notMem_empty _))

/-- The constructed HOL Light model already supplies full domains, an
infinite individual carrier and a selector. Kernel acceptance specializes to
that model without asking for a separate extensionality axiom. -/
theorem kernel_initialModel {sequent : Sequent} {certificate : SavedCertificate}
    (accepted : (savedChecker FirstOrder.Kernel.firstOrder).check
      (FirstOrder.renderSequent sequent) certificate = true) :
    ∃ φ, Translates [] sequent.concl.term .prop φ ∧
      ((∀ ψ ∈ translatedHypotheses sequent.hyp,
          ModelInterpretation.Controls.initialModel.{w}.models ψ) →
        ModelInterpretation.Controls.initialModel.{w}.models φ) :=
  kernel_models accepted ModelInterpretation.Controls.initialModel
    (HOL.HenkinModel.functionsRespectEqv_of_fullDomains
      ModelInterpretation.Controls.initialModel ModelInterpretation.Controls.initialModel_fullDomains)

end Kernel

namespace Controls

open Mettapedia.Languages.OpenTheory.ReachabilitySemantics

/-- A genuinely accepted source `REFL` graph has an MM0 certificate and a
truthful interpretation in the constructed source-family model. -/
theorem reflexivity_initialModel :
    ∃ certificate : SavedCertificate,
      (savedChecker FirstOrder.Kernel.firstOrder).check
        (FirstOrder.render ProofExecution.Controls.reflexivityTheorem) certificate = true ∧
      ∃ φ, Translates [] ProofExecution.Controls.reflexivityTheorem.sequent.concl.term .prop φ ∧
        ModelInterpretation.Controls.initialModel.{w}.models φ := by
  have checked := FirstOrder.Kernel.reflexivity_accepted
  obtain ⟨φ, translated, sound⟩ := kernel_initialModel checked
  refine ⟨_, checked, φ, translated, sound ?_⟩
  intro ψ member
  rcases member with ⟨hypothesis, member, _⟩
  exact absurd member (Finset.notMem_empty _)

/-- A concrete applicable model makes expanded falsity false. The general
semantic bridge therefore refuses every MM0 certificate for `⊢ F`. -/
theorem falsity_refused (certificate : SavedCertificate) :
    (savedChecker FirstOrder.Kernel.firstOrder).check
      (FirstOrder.renderSequent ⟨∅, falsity⟩) certificate = false := by
  exact refused_of_countermodel (axioms := [])
    (definition := FirstOrder.CalculusControls.validated) rfl
    (policy := emptyAxiomPolicy) (fun _ member => by cases member)
    (fun _ impossible => impossible.elim) FirstOrder.Kernel.firstOrder
    variableFreeSubstitutionClosed_empty (fun _ member => by cases member)
    ⟨∅, falsity⟩ PrimitiveSentences.falsityDB_translates twoPointModel
    twoPointModel_functionsRespectEqv
    (fun _ member => absurd member (Set.notMem_empty _))
    (fun _ member => by rcases member with ⟨_, member, _⟩; exact absurd member (Finset.notMem_empty _))
    twoPointModel_not_models_falsityFormula certificate

/-- Configuring a false axiom changes the accepted logic. The existing false
axiom is accepted by the actual saved checker, yet its independent translation
is false in the two-point model. Hence the model assumptions above matter. -/
theorem false_axiom_acceptance_has_no_unconditional_truth :
    (∃ certificate : SavedCertificate,
      (savedChecker (definition := FirstOrder.validatedHolCalculus [falsitySequent])
        (FirstOrder.holCalculus_firstOrder_axioms [falsitySequent])).check
        (FirstOrder.renderSequent falsitySequent) certificate = true) ∧
    ∀ φ, Translates [] falsitySequent.concl.term .prop φ →
      ¬ twoPointModel.models φ := by
  let : DecidablePred onlyFalsity := fun sequent =>
    inferInstanceAs (Decidable (sequent = falsitySequent))
  have derived : Derives (Rule onlyFalsity) falsityAxiom := by
    refine .node [] falsityAxiom (Or.inr ?_) (fun _ member => by cases member)
    exact ⟨falsitySequent, rfl, rfl, rfl, falsitySequent_isBool,
      (theorem_axiomResult_eq_iff_hasParts falsitySequent falsitySequent_isBool
        falsityAxiom).mp rfl⟩
  have accepted := (FirstOrder.savedChecker_exact (axioms := [falsitySequent])
    (definition := FirstOrder.validatedHolCalculus [falsitySequent]) rfl
    (policy := onlyFalsity)
    (fun sequent member => by
      have same : sequent = falsitySequent := by simpa using member
      cases same
      exact ⟨rfl, rfl, falsitySequent_isBool⟩)
    (fun sequent allowed => by simpa [onlyFalsity] using allowed)
    (FirstOrder.holCalculus_firstOrder_axioms [falsitySequent]) falsitySequent).mpr
      ⟨falsityAxiom, derived, rfl⟩
  refine ⟨accepted, ?_⟩
  intro φ translated
  rw [translated.unique_eq PrimitiveSentences.falsityDB_translates]
  exact twoPointModel_not_models_falsityFormula

/-- Extensional model truth is stronger than the axiom-free source closure:
eta is valid in every applicable model but has no saved MM0 certificate in
that configuration. Hosting exactness is not model completeness. -/
theorem eta_models_without_kernel_certificate (name : Name) (domain codomain : Ty) :
    ∃ φ, Translates [] (Eta.equation name domain codomain).term .prop φ ∧
      (∀ (model : HOL.HenkinModel.{0, 0, w} AtomicTy Symbol),
        model.FunctionsRespectEqv → model.models φ) ∧
      ∀ certificate : SavedCertificate,
        (savedChecker FirstOrder.Kernel.firstOrder).check
          (FirstOrder.renderSequent ⟨∅, Eta.equation name domain codomain⟩)
          certificate = false := by
  obtain ⟨φ, translated, provable⟩ := Eta.equation_translatedProvable name domain codomain
  refine ⟨φ, translated, ?_, ?_⟩
  · intro model extensional
    exact provable_models provable model extensional (fun ψ member => by
      rcases member with member | member
      · exact absurd member (Set.notMem_empty _)
      · rcases member with ⟨_, member, _⟩
        exact absurd member (Finset.notMem_empty _))
  · intro certificate
    rw [Bool.eq_false_iff]
    intro accepted
    obtain ⟨out, derived, same⟩ :=
      (FirstOrder.savedChecker_exact (axioms := [])
        (definition := FirstOrder.CalculusControls.validated) rfl
        (policy := emptyAxiomPolicy) (fun _ member => by cases member)
        (fun _ impossible => impossible.elim) FirstOrder.Kernel.firstOrder _).mp
          ⟨certificate, accepted⟩
    exact Eta.eta_not_derivable name domain codomain
      (derives_shared emptyAxiomPolicy derived) same

end Controls

end Mettapedia.Languages.HOLLight.MM0Meaning
