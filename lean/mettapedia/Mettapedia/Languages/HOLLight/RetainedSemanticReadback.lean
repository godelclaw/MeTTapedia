import Mettapedia.Languages.HOLLight.ProofSystem
import Mettapedia.Languages.OpenTheory.EtaCompleteness

/-!
# Source-judgment readback from HOL Light certificate acceptance

For closed intrinsic HOL formulas in the admitted signature image, acceptance
of the exact reversed sequent entails the original source judgment. The proof
uses the primitive-rule interpretation and the proved forward/reverse syntax
comparison. It applies to any accepted graph, not only graphs emitted by one
compiler.

The image condition excludes an uninterpreted constant named primitive
equality: the native checker gives that symbol its logical meaning. Assumption
sets can be read back into the supplied list, but their original occurrence or
proof identity cannot be reconstructed by this proposition-valued theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.RetainedSemanticReadback

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open ReverseTranslation EtaCompleteness

def sequent (hypotheses : List (HOL.ClosedFormula Symbol)) (conclusion : HOL.ClosedFormula Symbol) : Sequent :=
  ⟨reverseHypotheses Naming.empty hypotheses, reverseCanonical Naming.empty conclusion⟩

private theorem reverse_translation (formula : HOL.ClosedFormula Symbol)
    (free : EqualitySymbolFree formula) :
    ∃ translated : HOL.ClosedFormula Symbol,
      Translates [] (reverseCanonical Naming.empty formula).term .prop translated ∧
      HOL.ExtDerivation Symbol [translated] formula ∧
      HOL.ExtDerivation Symbol [formula] translated := by
  obtain ⟨translated, interpretation, forward, backward⟩ :=
    exists_translates_reverseTermOpen_derivable formula free
  exact ⟨translated, by simpa only [reverseCanonical, reverseTerm_eq_reverseTermOpen] using interpretation,
    forward, backward⟩

theorem source_of_translatedProvable
    (hypotheses : List (HOL.ClosedFormula Symbol)) (conclusion : HOL.ClosedFormula Symbol)
    (hypothesesFree : ∀ formula ∈ hypotheses, EqualitySymbolFree formula)
    (conclusionFree : EqualitySymbolFree conclusion)
    (accepted : TranslatedProvable ∅ (sequent hypotheses conclusion)) :
    HOL.ExtDerivation Symbol hypotheses conclusion := by
  obtain ⟨translated, interpretation, derived⟩ := accepted
  obtain ⟨readback, readbackTranslation, conclusionFrom, _⟩ := reverse_translation conclusion conclusionFree
  have same : translated = readback := interpretation.unique_eq readbackTranslation
  subst translated
  let theory : HOL.ClosedTheorySet Symbol := {formula | formula ∈ hypotheses}
  have transported : HOL.ClosedTheorySet.Provable theory readback :=
    provable_of_forall_provable derived (by
      intro formula member
      rcases member with impossible | member
      · exact False.elim impossible
      · obtain ⟨native, nativeMember, nativeTranslation⟩ := member
        obtain ⟨original, originalMember, rfl⟩ := mem_reverseHypotheses.mp nativeMember
        obtain ⟨originalTranslation, originalTranslated, _, originalTo⟩ :=
          reverse_translation original (hypothesesFree original originalMember)
        have equal : formula = originalTranslation := nativeTranslation.unique_eq originalTranslated
        subst formula
        apply provable_of_extDerivation originalTo
        intro premise present
        have samePremise : premise = original := List.mem_singleton.mp present
        subst premise
        exact HOL.ClosedTheorySet.provable_of_mem originalMember)
  have result : HOL.ClosedTheorySet.Provable theory conclusion :=
    provable_of_extDerivation conclusionFrom (by
      intro premise member
      have samePremise : premise = readback := List.mem_singleton.mp member
      subst premise
      exact transported)
  obtain ⟨premises, included, derivation⟩ := result
  exact HOL.ExtDerivation.mono (fun member => included _ member) derivation

/-- Any accepted exact native sequent in the admitted image has a source
derivation. Eta is a declared policy axiom, not an unrecorded conversion. -/
theorem accepted_source
    (hypotheses : List (HOL.ClosedFormula Symbol)) (conclusion : HOL.ClosedFormula Symbol)
    (hypothesesFree : ∀ formula ∈ hypotheses, EqualitySymbolFree formula)
    (conclusionFree : EqualitySymbolFree conclusion)
    {claim : Theorem} {certificate : ProofSystem.Certificate}
    [DecidablePred etaAxiomPolicy]
    (accepted : (ProofSystem.checker etaAxiomPolicy).check claim certificate = true)
    (exactSequent : claim.sequent = sequent hypotheses conclusion) :
    HOL.ExtDerivation Symbol hypotheses conclusion := by
  have native := derives_shared etaAxiomPolicy
    ((ProofSystem.checker_authority etaAxiomPolicy).sound claim certificate accepted)
  have source := (derives_etaAxiomPolicy_iff_translatedProvable
    (sequent := sequent hypotheses conclusion)
    (fun _ member => isBool_of_mem_reverseHypotheses member)).mp ⟨claim, native, exactSequent⟩
  exact source_of_translatedProvable hypotheses conclusion hypothesesFree conclusionFree source

universe u

/-- The read-back derivation is sound in every supplied extensional Henkin
model. No separate validity premise for the accepted conclusion is required. -/
theorem accepted_models
    (hypotheses : List (HOL.ClosedFormula Symbol)) (conclusion : HOL.ClosedFormula Symbol)
    (hypothesesFree : ∀ formula ∈ hypotheses, EqualitySymbolFree formula)
    (conclusionFree : EqualitySymbolFree conclusion)
    {claim : Theorem} {certificate : ProofSystem.Certificate}
    [DecidablePred etaAxiomPolicy]
    (accepted : (ProofSystem.checker etaAxiomPolicy).check claim certificate = true)
    (exactSequent : claim.sequent = sequent hypotheses conclusion)
    (model : HOL.HenkinModel.{0, 0, u} AtomicTy Symbol)
    (respects : model.FunctionsRespectEqv)
    (satisfied : ∀ formula ∈ hypotheses, model.models formula) : model.models conclusion :=
  HOL.Soundness.extDerivation_sound
    (accepted_source hypotheses conclusion hypothesesFree conclusionFree accepted exactSequent)
    respects (fun index => nomatch index) satisfied

end Mettapedia.Languages.HOLLight.RetainedSemanticReadback
