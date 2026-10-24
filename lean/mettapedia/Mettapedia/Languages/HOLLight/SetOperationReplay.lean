import Mettapedia.Languages.HOLLight.SetOperationInterpretation
import Mettapedia.Logic.HOL.Embedding.CodedHypersetInterpretation
import Mettapedia.Logic.HOL.Embedding.HypersetHOLTermInterpretation
import Mettapedia.Logic.HOL.Embedding.ZFSetHOLTermInterpretation

/-!
# Checked HOL Light sequents in set and hyperset interpretations

The native claim contains the exact compiled common-profile assumptions and
conclusion. Acceptance implies truth in the independently constructed set,
well-founded hyperset, full hyperset and coded hyperset models, whenever the
listed assumptions hold there. The graph interpretation corollaries use the
actual material function graphs, not a second evaluator defined by transport.

Membership induction and its negation cannot be checked from the six common
operation axioms under the eta-only policy. The two concrete models separate
those extensions while sharing the same native symbol declarations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.HOLLight.SetOperationReplay

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open HOL.Embedding
open Mettapedia.TypeTheory.MaterialSets.Hypersets

universe u

abbrev Formula := HOL.ClosedFormula ZFSetHenkinInterpretation.Symbol

def expanded (formula : Formula) : HOL.ClosedFormula Symbol :=
  HOL.ImpredicativeConnectives.expand (SetOperationInterpretation.term formula)

def sequent (hypotheses : List Formula) (conclusion : Formula) : Sequent :=
  RetainedSemanticReadback.sequent (hypotheses.map expanded) (expanded conclusion)

variable {hypotheses : List Formula} {conclusion : Formula}
  {claim : Theorem} {certificate : ProofSystem.Certificate} [DecidablePred etaAxiomPolicy]

theorem accepted_sets
    (accepted : (ProofSystem.checker etaAxiomPolicy).check claim certificate = true)
    (exactSequent : claim.sequent = sequent hypotheses conclusion)
    (satisfied : ∀ formula ∈ hypotheses, ZFSetHenkinInterpretation.model.{u}.models formula) :
    ZFSetHenkinInterpretation.model.{u}.models conclusion :=
  SetOperationInterpretation.accepted_meaning ZFSet.{u} ∅ ZFSetHenkinInterpretation.denoteSymbol
    hypotheses conclusion accepted exactSequent satisfied

theorem accepted_wellFounded (presentation : HSet.Presentation.{u})
    (accepted : (ProofSystem.checker etaAxiomPolicy).check claim certificate = true)
    (exactSequent : claim.sequent = sequent hypotheses conclusion)
    (satisfied : ∀ formula ∈ hypotheses, (WellFoundedHypersetInterpretation.model presentation).models formula) :
    (WellFoundedHypersetInterpretation.model presentation).models conclusion :=
  SetOperationInterpretation.accepted_meaning WellFoundedPart.{u} WellFoundedPart.empty
    (WellFoundedHypersetInterpretation.denoteSymbol presentation)
    hypotheses conclusion accepted exactSequent satisfied

theorem accepted_hypersets (presentation : HSet.Presentation.{u})
    (accepted : (ProofSystem.checker etaAxiomPolicy).check claim certificate = true)
    (exactSequent : claim.sequent = sequent hypotheses conclusion)
    (satisfied : ∀ formula ∈ hypotheses, (HypersetHenkinInterpretation.model presentation).models formula) :
    (HypersetHenkinInterpretation.model presentation).models conclusion :=
  SetOperationInterpretation.accepted_meaning HSet.{u} ∅ (HypersetHenkinInterpretation.denoteSymbol presentation)
    hypotheses conclusion accepted exactSequent satisfied

theorem accepted_codes (presentation : HSet.Presentation.{u})
    (accepted : (ProofSystem.checker etaAxiomPolicy).check claim certificate = true)
    (exactSequent : claim.sequent = sequent hypotheses conclusion)
    (satisfied : ∀ formula ∈ hypotheses, (CodedHypersetInterpretation.model presentation).models formula) :
    (CodedHypersetInterpretation.model presentation).models conclusion := by
  apply (CodedHypersetInterpretation.models_iff presentation conclusion).mpr
  apply accepted_hypersets presentation accepted exactSequent
  intro formula member
  exact (CodedHypersetInterpretation.models_iff presentation formula).mp (satisfied formula member)

/-- The semantic theorem applies to the actual all-constructor compiler. -/
theorem compiled_sequent (source : HOL.ProofSyntax ZFSetHenkinInterpretation.Symbol hypotheses conclusion)
    (origin : ProofExecution.Origin) :
    (SetOperationInterpretation.compile etaAxiomPolicy rfl source ReverseTranslation.Naming.empty origin).proof.result.sequent =
      sequent hypotheses conclusion := by
  apply (SetOperationInterpretation.compile_sequent etaAxiomPolicy rfl source
    ReverseTranslation.Naming.empty origin).trans
  apply Sequent.ext
  · apply congrArg (ReverseTranslation.reverseHypotheses ReverseTranslation.Naming.empty)
    rw [List.map_map]
    apply List.map_congr_left
    intro formula _
    rfl
  · rfl

theorem compiled_hyperset_sound (presentation : HSet.Presentation.{u})
    (source : HOL.ProofSyntax ZFSetHenkinInterpretation.Symbol hypotheses conclusion)
    (origin : ProofExecution.Origin)
    (satisfied : ∀ formula ∈ hypotheses, (HypersetHenkinInterpretation.model presentation).models formula) :
    (HypersetHenkinInterpretation.model presentation).models conclusion :=
  accepted_hypersets presentation
    (SetOperationInterpretation.compile_accepted etaAxiomPolicy rfl source ReverseTranslation.Naming.empty origin)
    (compiled_sequent source origin) satisfied

/-- Acceptance feeds the actual graph-based material evaluator. -/
theorem accepted_hyperset_graph (presentation : HSet.Presentation.{u})
    (accepted : (ProofSystem.checker etaAxiomPolicy).check claim certificate = true)
    (exactSequent : claim.sequent = sequent hypotheses conclusion)
    (satisfied : ∀ formula ∈ hypotheses, (HypersetHenkinInterpretation.model presentation).models formula) :
    ZFSetHOLTypeInterpretation.holds
      (HypersetHOLTermInterpretation.interpret presentation conclusion (fun index => nomatch index)) := by
  have meaning := HypersetHOLTermInterpretation.term_agreement presentation conclusion (fun index => nomatch index)
  have truth := accepted_hypersets presentation accepted exactSequent satisfied
  change (HypersetHOLTypeInterpretation.decode .prop _).down
  rw [meaning]
  have empty : (HypersetHOLTermInterpretation.decodeValuation (Γ := []) (fun index => nomatch index) :
      (HypersetHenkinInterpretation.model presentation).Valuation []) =
      (fun {A} (index : HOL.Var [] A) => nomatch index) := by
    funext A index
    nomatch index
  rw [empty]
  have propositionEqual : (HypersetHenkinInterpretation.model presentation).models conclusion =
      ((HypersetHenkinInterpretation.model presentation).denote conclusion
        (fun {A} (index : HOL.Var [] A) => nomatch index)).down := by
    unfold HOL.HenkinModel.models HOL.PreModel.models
    apply congrArg (fun valuation : (HypersetHenkinInterpretation.model presentation).Valuation [] =>
      ((HypersetHenkinInterpretation.model presentation).denote conclusion valuation).down)
    funext A index
    nomatch index
  exact propositionEqual.mp truth

theorem foundation_refused (presentation : HSet.Presentation.{u})
    (exactSequent : claim.sequent = sequent HypersetHenkinInterpretation.operationTheory
      ZFSetHenkinInterpretation.setInduction) :
    (ProofSystem.checker etaAxiomPolicy).check claim certificate ≠ true :=
  fun accepted => HypersetHenkinInterpretation.setInduction_invalid presentation
    (accepted_hypersets presentation accepted exactSequent
      (HypersetHenkinInterpretation.operationTheory_valid presentation))

theorem negatedInduction_refused (presentation : HSet.Presentation.{u})
    (exactSequent : claim.sequent = sequent HypersetHenkinInterpretation.operationTheory
      (.not ZFSetHenkinInterpretation.setInduction)) :
    (ProofSystem.checker etaAxiomPolicy).check claim certificate ≠ true := by
  intro accepted
  exact accepted_wellFounded presentation accepted exactSequent
    (HypersetHenkinInterpretation.wellFounded_operationTheory_valid presentation)
    (WellFoundedHypersetInterpretation.setInduction_valid presentation)

end Mettapedia.Languages.HOLLight.SetOperationReplay
