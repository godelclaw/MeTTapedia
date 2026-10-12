import Mettapedia.OSLF.Framework.RhoScopedInstrumentAdmissionControls
import Mettapedia.OSLF.Syntax.RhoScopedChannelSeparation

/-!
# A partial original observer does not admit arbitrary contextual replacement

Two distinct open names agree for the kit with no structural instruments.
Putting either name in the channel position of an actual output changes
whether a supplied matching input enables original communication. The
distinguishing formula contains one proper interaction and no structural
test. Thus partial-kit adequacy is not an arbitrary binding-context
congruence theorem.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.RhoScopedPartialObserverControls

open _root_.CategoryTheory Mettapedia.OSLF.Binding
open RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls ScopedEncoding
open RhoIntrinsicReadback
open RhoScopedInstrumentProperBase RhoScopedInstrumentAdmissionControls
open RhoScopedParallelEvents RhoScopedParallelReactiveSystem RhoScopedChannelSeparation
open RhoScopedFiringSubstitutionControls (context firstName secondName firstInput originalRoot original_source)

local instance (scope : Ctx sig) : DecidableEq (RhoScopedParallelInventory.Prime scope) := Classical.decEq _
local instance : Quiver (Scope sig) := bindingFrameQuiver sig

def firstOutput : Term sig context Srt.pr := outputRaw (.var .zero) null
def secondOutput : Term sig context Srt.pr := outputRaw (.var (.succ .zero)) null

def matching : Firing (rules := sourceRules) (admitted := core)
    (project firstOutput) firstInput (zero context) where
  root := originalRoot
  surrounding := zero context
  square := original_source.symm.trans (join_zero_right originalRoot.source).symm
  least := by rw [RhoScopedParallelInventory.read_zero, Multiset.inter_zero]
  target := (join_zero_right (zero context)).symm

def question : ScopedInstruments.Formula sig (base core).Atom (base core).Label (context, Srt.pr) :=
  @SortedInstrumentCongruence.Formula.proper (signature sig) (base core).Atom (base core).Label
    (context, Srt.pr) ⟨context, firstInput⟩ (context, Srt.pr) SortedInstrumentCongruence.Formula.top

theorem question_allowed : SortedInstrumentCongruence.Formula.Allowed noStructuralInstruments question :=
  fun absent => absent.elim

theorem first_output_answers : ScopedInstruments.Holds (base core) question firstOutput := by
  refine ⟨null, (proper_iff_complete_firing core firstInput firstOutput _).mpr ⟨matching⟩, ?_⟩
  exact fun absent => absent.elim

theorem second_output_cannot_answer : ¬ ScopedInstruments.Holds (base core) question secondOutput := by
  rintro ⟨target, actual, _postcondition⟩
  obtain ⟨receipt⟩ := (proper_iff_complete_firing core firstInput secondOutput target).mp actual
  have event : RhoScopedParallelEvents.Step (rules := sourceRules) (admitted := core)
      (join (project secondOutput) firstInput) (project target) :=
    (step_iff_root_surrounding _ _).mpr
      ⟨receipt.root, receipt.surrounding, receipt.square, receipt.target⟩
  have names := channels_agree_of_original_reaction secondName firstName
    (zero context) (zero (Srt.nm :: context)) event
  exact RhoScopedFiringSubstitutionControls.original_names_distinct names.symm

theorem output_answers_differ :
    ¬ ScopedInstruments.LogicallyEquivalent (base core) noStructuralInstruments firstOutput secondOutput :=
  fun equivalent => second_output_cannot_answer ((equivalent question question_allowed).mp first_output_answers)

theorem outputs_are_not_bisimilar :
    ¬ ScopedInstruments.Bisimilar (base core) noStructuralInstruments (.term firstOutput) (.term secondOutput) :=
  fun related => output_answers_differ
    ((instrumented_partial_adequacy core noStructuralInstruments _ _).mpr related)

def outputFrame : BindingFrame sig (context, Srt.nm) (context, Srt.pr) :=
  .slot context Srt.pr Op.out 0 (Fin.cases (fun absent => False.elim (absent rfl))
    (fun previous _ => by
      have only : previous = 0 := @Subsingleton.elim (Fin 1) inferInstance previous 0
      subst previous
      exact null))

def outputContext : BindingContext sig (context, Srt.nm) (context, Srt.pr) :=
  RhoScopedEquationContextControls.single outputFrame

theorem partial_agreement_is_not_contextual_replacement :
    ScopedInstruments.Bisimilar (base core) noStructuralInstruments
      (.term (.var (.zero : Var context Srt.nm))) (.term (.var (show Var context Srt.nm from .succ .zero))) ∧
    ¬ ScopedInstruments.Bisimilar (base core) noStructuralInstruments
      (.term (fillContext outputContext (.var (.zero : Var context Srt.nm))))
      (.term (fillContext outputContext (.var (.succ .zero)))) :=
  ⟨names_related_with_no_structural_instruments core _ _, outputs_are_not_bisimilar⟩

end Mettapedia.OSLF.Framework.RhoScopedPartialObserverControls
