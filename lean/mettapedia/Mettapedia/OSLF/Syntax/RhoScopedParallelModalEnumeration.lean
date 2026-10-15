import Mettapedia.OSLF.Syntax.RhoScopedParallelModalAdequacy
import Mettapedia.OSLF.MeTTaIL.PatternCountability
import Mettapedia.GSLT.Logic.HennessyMilnerCountability

/-!
# Complete finite-question enumerations for original scoped rho labels

The actual source-equation process carrier is countable by its earned
injection into the complete authored pattern syntax. A separately formed
ordinary HML syntax maps onto the interface-indexed parallel question grammar.
This earns countability and a complete enumeration of those actual questions.
The enumeration is a mathematical construction, not a runtime decider or a
branching hypothesis; no enumeration independence of numerical ranks is claimed.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Binding.RhoScopedParallelModalEnumeration

open _root_.CategoryTheory RhoSchema RhoQuotationClassFibres RhoScopedParallelContexts
open RhoScopedParallelModalAdequacy
open RhoIntrinsicReadback

instance (context : Ctx sig) : Countable (Process context) :=
  (canonical_encoding_injective context Srt.pr).countable

abbrev OrdinaryQuestion (context : Ctx sig) :=
  Mettapedia.GSLT.HennessyMilner.Formula PEmpty.{1} (Process context)

def question {context : Ctx sig} {atInterface : ContextCategory context} :
    OrdinaryQuestion context →
      Mettapedia.GSLT.InterfaceModalLogic.Formula (ContextCategory context) atInterface
  | .top => .top
  | .atom absent => absent.elim
  | .conj first second => .conj (question first) (question second)
  | .neg inner => .neg (question inner)
  | .dia label inner => .diamond (last := atInterface) ⟨label⟩ (question inner)

theorem question_surjective {context : Ctx sig} {atInterface : ContextCategory context} :
    Function.Surjective (question (context := context) (atInterface := atInterface)) := by
  intro formula
  induction formula with
  | top => exact ⟨.top, rfl⟩
  | conj first second firstCovered secondCovered =>
      obtain ⟨firstQuestion, firstRead⟩ := firstCovered
      obtain ⟨secondQuestion, secondRead⟩ := secondCovered
      exact ⟨.conj firstQuestion secondQuestion, congrArg₂
        (Mettapedia.GSLT.InterfaceModalLogic.Formula.conj) firstRead secondRead⟩
  | neg inner covered =>
      obtain ⟨innerQuestion, readout⟩ := covered
      exact ⟨.neg innerQuestion, congrArg
        Mettapedia.GSLT.InterfaceModalLogic.Formula.neg readout⟩
  | @diamond first last label inner covered =>
      cases first
      cases last
      obtain ⟨innerQuestion, readout⟩ := covered
      refine ⟨.dia label.process innerQuestion, ?_⟩
      change Mettapedia.GSLT.InterfaceModalLogic.Formula.diamond label
        (question innerQuestion) = _
      exact congrArg (Mettapedia.GSLT.InterfaceModalLogic.Formula.diamond label) readout

instance (context : Ctx sig) : Countable (Finitary.Formula context) :=
  (question_surjective (context := context) (atInterface := interface context)).countable

instance (context : Ctx sig) : Nonempty (Finitary.Formula context) := ⟨.top⟩

def enumeration (context : Ctx sig) : Nat → Finitary.Formula context :=
  (exists_surjective_nat (Finitary.Formula context)).choose

theorem enumeration_covers (context : Ctx sig) : Function.Surjective (enumeration context) :=
  (exists_surjective_nat (Finitary.Formula context)).choose_spec

theorem every_question_has_an_index {context : Ctx sig} (formula : Finitary.Formula context) :
    ∃ index, enumeration context index = formula := enumeration_covers context formula

end Mettapedia.OSLF.Binding.RhoScopedParallelModalEnumeration
