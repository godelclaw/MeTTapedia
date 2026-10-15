import Mettapedia.OSLF.Syntax.RhoScopedParallelSourceAdequacy
import Mettapedia.GSLT.Logic.InterfaceModalAdequacy

/-!
# Modal adequacy of original scoped rho least-context observations

The reading is defined independently from the computed missing partner and
the independently authored root instance. It is compared with the actual
IPO semantics at every ambient binding scope. Complete conjunctions earn
adequacy without a branching hypothesis. Finitary adequacy uses an explicit
finite cover of the computed successor classes by their proved behavior.

These are literal parallel-context labels on the original equation quotient.
Behavioral matching of reflective payloads and a wider observer context
class retain their separate admission obligations.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Binding.RhoScopedParallelModalAdequacy

open _root_.CategoryTheory RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls
open RhoScopedParallelContexts
open RhoScopedParallelEvents RhoScopedParallelReactiveSystem
open Mettapedia.GSLT.RedexRelativeCongruence

namespace Complete

universe u

variable {Index : Type u} (rules : Index → ProcessRule) (admitted : Index → Prop)
  {context : Ctx sig}

abbrev Formula (context : Ctx sig) :=
  Mettapedia.GSLT.InterfaceInfinitaryModalLogic.Formula (ContextCategory context) (interface context)

/-- Interpret the formula by actual computed root firings, not by bisimilarity. -/
def Holds : {atInterface : ContextCategory context} →
    Mettapedia.GSLT.InterfaceInfinitaryModalLogic.Formula (ContextCategory context) atInterface →
    Process context → Prop
  | _, .conj parts, first => ∀ index, Holds (parts index) first
  | _, .neg inner, first => ¬ Holds inner first
  | _, .diamond label inner, first =>
      ∃ root : Root rules admitted context,
        label.process = leastLabel first root ∧
          Holds inner (join root.target (reactionRemainder first root))

theorem holds_iff_interface {atInterface : ContextCategory context}
    (formula : Mettapedia.GSLT.InterfaceInfinitaryModalLogic.Formula
      (ContextCategory context) atInterface) :
    ∀ first : Process context, Holds rules admitted formula first ↔
      Mettapedia.GSLT.InterfaceInfinitaryModalLogic.Holds
        (reactionRules rules admitted) formula (arrow first) := by
  induction formula with
  | conj parts readings =>
      intro first
      exact forall_congr' (fun index => readings index first)
  | neg inner reading => intro first; exact not_congr (reading first)
  | diamond label inner reading =>
      intro first
      constructor
      · rintro ⟨root, labelRead, nextHolds⟩
        refine ⟨arrow (join root.target (reactionRemainder first root)), ?_,
          (reading _).mp nextHolds⟩
        exact (actIPO_iff_computed first label.process _).mpr ⟨root, labelRead, rfl⟩
      · rintro ⟨next, firing, nextHolds⟩
        obtain ⟨root, labelRead, nextRead⟩ :=
          (actIPO_iff_computed first label.process next.process).mp firing
        exact ⟨root, labelRead, nextRead ▸ (reading next.process).mpr nextHolds⟩

def LogicallyEquivalent (first second : Process context) : Prop :=
  ∀ formula : Formula context,
    Holds rules admitted formula first ↔ Holds rules admitted formula second

theorem logicallyEquivalent_iff_interface (first second : Process context) :
    LogicallyEquivalent rules admitted first second ↔
      Mettapedia.GSLT.InterfaceInfinitaryModalLogic.LogicallyEquivalent
        (reactionRules rules admitted) (arrow first) (arrow second) :=
  forall_congr' (fun formula => iff_congr
    (holds_iff_interface rules admitted formula first)
    (holds_iff_interface rules admitted formula second))

/-- Actual computed observations characterize the actual IPO behavior, without finite branching. -/
theorem logicallyEquivalent_iff_bisimilar (first second : Process context) :
    LogicallyEquivalent rules admitted first second ↔
      Bisimilar (rules := rules) (admitted := admitted) first second :=
  (logicallyEquivalent_iff_interface rules admitted first second).trans
    (Mettapedia.GSLT.InterfaceInfinitaryModalLogic.logicallyEquivalent_iff_ipoBisimilar _ _ _)

theorem context_congruence {first second : Process context}
    (related : LogicallyEquivalent rules admitted first second) (surrounding : Process context) :
    LogicallyEquivalent rules admitted (join first surrounding) (join second surrounding) :=
  (logicallyEquivalent_iff_bisimilar rules admitted _ _).mpr
    (RhoScopedParallelReactiveSystem.context_congruence
      ((logicallyEquivalent_iff_bisimilar rules admitted _ _).mp related) surrounding)

/-- A least-labelled firing supplies an actual independently authored event after adjoining its label. -/
theorem actIPO_enables_event (first label second : Process context)
    (firing : ActIPO (reactionRules rules admitted) (arrow label) (arrow first) (arrow second)) :
    RhoScopedParallelEvents.Step (rules := rules) (admitted := admitted)
      (join first label) second := by
  obtain ⟨receipt⟩ := (firing_iff_actIPO first label second).mpr firing
  exact (step_iff_root_surrounding _ _).mpr
    ⟨receipt.root, receipt.surrounding, receipt.square, receipt.target⟩

theorem diamond_supplies_actual_event (label : Process context) (formula : Formula context)
    (first : Process context) (holds : Holds rules admitted (.diamond (arrow label) formula) first) :
    ∃ second, RhoScopedParallelEvents.Step (rules := rules) (admitted := admitted)
      (join first label) second ∧ Holds rules admitted formula second := by
  obtain ⟨next, firing, postcondition⟩ :=
    (holds_iff_interface rules admitted _ first).mp holds
  exact ⟨next.process, actIPO_enables_event rules admitted first label next.process firing,
    (holds_iff_interface rules admitted formula next.process).mpr postcondition⟩

theorem identity_diamond_iff (formula : Formula context) (first : Process context) :
    Holds rules admitted (.diamond (𝟙 (interface context)) formula) first ↔
      ∃ second, RhoScopedParallelEvents.Step (rules := rules) (admitted := admitted) first second ∧
        Holds rules admitted formula second := by
  rw [holds_iff_interface]
  change (∃ next, ActIPO (reactionRules rules admitted) (𝟙 (interface context))
      (arrow first) next ∧ _) ↔ _
  constructor
  · rintro ⟨next, firing, holds⟩
    exact ⟨next.process, (step_iff_actIPO_identity _ _).mpr firing,
      (holds_iff_interface rules admitted formula next.process).mpr holds⟩
  · rintro ⟨second, firing, holds⟩
    exact ⟨arrow second, (step_iff_actIPO_identity _ _).mp firing,
      (holds_iff_interface rules admitted formula second).mp holds⟩

/-- At the closed scope, the modal postcondition is attached to an actual printed source step. -/
theorem identity_diamond_source_iff (formula : Formula []) (source : Term sig [] Srt.pr) :
    Holds sourceRules withReflection (.diamond (𝟙 (interface [])) formula) (project source) ↔
      ∃ target : Term sig [] Srt.pr, ParallelStepModE source target ∧
        Holds sourceRules withReflection formula (project target) := by
  rw [identity_diamond_iff]
  constructor
  · rintro ⟨second, firing, holds⟩
    induction second using Quotient.inductionOn with
    | _ target => exact ⟨target,
        RhoScopedParallelSourceAdequacy.event_to_parallelStepModE firing, holds⟩
  · rintro ⟨target, firing, holds⟩
    exact ⟨project target,
      RhoScopedParallelSourceAdequacy.parallelStepModE_to_event firing, holds⟩

end Complete

namespace Finitary

universe u

variable {Index : Type u} (rules : Index → ProcessRule) (admitted : Index → Prop)
  {context : Ctx sig}

abbrev Formula (context : Ctx sig) :=
  Mettapedia.GSLT.InterfaceModalLogic.Formula (ContextCategory context) (interface context)

/-- The finite grammar retains the same independently computed root interpretation. -/
def Holds (formula : Formula context) (first : Process context) : Prop :=
  Complete.Holds rules admitted
    (Mettapedia.GSLT.InterfaceInfinitaryModalLogic.ofFinitary formula) first

theorem holds_iff_interface (formula : Formula context) (first : Process context) :
    Holds rules admitted formula first ↔ Mettapedia.GSLT.InterfaceModalLogic.Holds
      (reactionRules rules admitted) formula (arrow first) :=
  (Complete.holds_iff_interface rules admitted _ first).trans
    (Mettapedia.GSLT.InterfaceInfinitaryModalLogic.holds_ofFinitary _ formula _)

def LogicallyEquivalent (first second : Process context) : Prop :=
  ∀ formula : Formula context,
    Holds rules admitted formula first ↔ Holds rules admitted formula second

theorem logicallyEquivalent_iff_interface (first second : Process context) :
    LogicallyEquivalent rules admitted first second ↔
      Mettapedia.GSLT.InterfaceModalLogic.LogicallyEquivalent
        (reactionRules rules admitted) (arrow first) (arrow second) :=
  forall_congr' (fun formula => iff_congr
    (holds_iff_interface rules admitted formula first)
    (holds_iff_interface rules admitted formula second))

/-- Finitary soundness needs no successor-cover assumption. -/
theorem logicallyEquivalent_of_bisimilar {first second : Process context}
    (related : Bisimilar (rules := rules) (admitted := admitted) first second) :
    LogicallyEquivalent rules admitted first second :=
  (logicallyEquivalent_iff_interface rules admitted first second).mpr
    (Mettapedia.GSLT.InterfaceModalLogic.logicallyEquivalent_of_ipoBisimilar _ related)

/-- A finite cover of all actual computed root successors, by their earned behavior. -/
def FiniteSuccessorCover (context : Ctx sig) : Prop :=
  ∀ (first label : Process context),
    ∃ representatives : Set (Process context), representatives.Finite ∧
      ∀ root : Root rules admitted context, label = leastLabel first root →
        ∃ representative ∈ representatives,
          Bisimilar (rules := rules) (admitted := admitted)
            (join root.target (reactionRemainder first root)) representative

theorem finite_cover_earns_interface (finite : FiniteSuccessorCover rules admitted context) :
    Mettapedia.GSLT.InterfaceModalLogic.ImageFiniteBisimilar
      (reactionRules (context := context) rules admitted) := by
  intro firstInterface lastInterface label first
  obtain ⟨representatives, hFinite, covers⟩ := finite first.process label.process
  refine ⟨arrow '' representatives, hFinite.image arrow, ?_⟩
  intro target firing
  obtain ⟨root, labelRead, targetRead⟩ :=
    (actIPO_iff_computed first.process label.process target.process).mp firing
  obtain ⟨representative, member, related⟩ := covers root labelRead
  refine ⟨arrow representative, ⟨representative, member, rfl⟩, ?_⟩
  change Bisimilar (rules := rules) (admitted := admitted) target.process representative
  rw [targetRead]
  exact related

theorem logicallyEquivalent_iff_bisimilar (finite : FiniteSuccessorCover rules admitted context)
    (first second : Process context) :
    LogicallyEquivalent rules admitted first second ↔
      Bisimilar (rules := rules) (admitted := admitted) first second :=
  (logicallyEquivalent_iff_interface rules admitted first second).trans
    (Mettapedia.GSLT.InterfaceModalLogic.logicallyEquivalent_iff_ipoBisimilar_of_behavioral_cover
      _ (finite_cover_earns_interface rules admitted finite) _ _)

theorem logicallyEquivalent_iff_complete (finite : FiniteSuccessorCover rules admitted context)
    (first second : Process context) :
    LogicallyEquivalent rules admitted first second ↔ Complete.LogicallyEquivalent rules admitted first second :=
  (logicallyEquivalent_iff_bisimilar rules admitted finite first second).trans
    (Complete.logicallyEquivalent_iff_bisimilar rules admitted first second).symm

end Finitary

end Mettapedia.OSLF.Binding.RhoScopedParallelModalAdequacy
