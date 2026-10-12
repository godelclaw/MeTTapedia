import Mettapedia.OSLF.Syntax.RhoScopedNameSeparatedDecomposition
import Mettapedia.OSLF.Syntax.RhoScopedScopeDecompositionControls

/-!
# An actual unnamed rho component can move between separated scopes

The original source quotient has a nonzero drop of the quoted null process.
Its canonical channel support is empty. Adjoining it to either of two
channel-separated output scopes gives the same quoted whole with different
halves. Both scope name images are disjoint, and all the relevant process
bodies have faithful quotation readback. Thus name separation alone does
not earn the component-detection condition used by the positive theorem.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoScopedScopeUnnamedControls

open RhoSchema RhoQuotationClassFibres RhoScopedParallelInventory RhoScopedScopeDecomposition
open RhoScopedScopeDecompositionControls RhoScopedNameSeparatedDecomposition
open RhoSchema.IntrinsicEncoding RhoIntrinsicCanonicalBag
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context

def idle : Process [] := drop (quote (zero []))

def idlePrime : Prime [] :=
  ⟨encodeEquationClass idle, contents_prime idle (by decide +kernel)⟩

theorem read_idle : read idle = {idlePrime} := by
  apply values_injective []
  rw [values_read, components_bagContents]
  decide +kernel

theorem idle_support_empty : channelSupport idle = ∅ := by
  change freeNames (.apply "PDrop" [.apply "NQuote" [.apply "PZero" []]]) = ∅
  simp [freeNames]

theorem first_channel : channelSupport firstOutput =
    {encodeEquationClass (quote (zero []))} := by
  change freeNames (.apply "POutput" [encodeEquationClass (quote (zero [])),
    .apply "PZero" []]) = _
  simp [freeNames]

theorem second_channel : channelSupport secondOutput =
    {encodeEquationClass (quote visible)} := by
  change freeNames (.apply "POutput" [encodeEquationClass (quote visible),
    .apply "PZero" []]) = _
  simp [freeNames]

def leftChoice (process : Process []) : Prop :=
  process = repeatedLeft ∨ process = join repeatedLeft idle

def rightChoice (process : Process []) : Prop :=
  process = secondOutput ∨ process = join secondOutput idle

theorem left_channel {process : Process []} (admitted : leftChoice process) :
    channelSupport process = {encodeEquationClass (quote (zero []))} := by
  rcases admitted with rfl | rfl <;>
    simp [repeatedLeft, channelSupport_join, first_channel, idle_support_empty]

theorem right_channel {process : Process []} (admitted : rightChoice process) :
    channelSupport process = {encodeEquationClass (quote visible)} := by
  rcases admitted with rfl | rfl <;>
    simp [channelSupport_join, second_channel, idle_support_empty]

theorem complete_scope_channel_supports_are_disjoint : NameSeparated leftChoice rightChoice := by
  intro first second firstAdmitted secondAdmitted
  rw [left_channel firstAdmitted, right_channel secondAdmitted]
  exact Set.disjoint_singleton.mpr (by decide +kernel)

theorem left_bodies_exposed {process : Process []} (admitted : leftChoice process) : Exposed process := by
  apply exposed_of_component_count_ne_one
  rcases admitted with rfl | rfl
  · rw [left_occurrences]
    decide
  · rw [read_join, Multiset.card_add, left_occurrences, read_idle, Multiset.card_singleton]
    decide

theorem right_bodies_exposed {process : Process []} (admitted : rightChoice process) : Exposed process := by
  rcases admitted with rfl | rfl
  · change RhoFiniteQuotationOrigins.dropBody (encodeEquationClass secondOutput) = none
    decide +kernel
  · apply exposed_of_component_count_ne_one
    rw [read_join, Multiset.card_add, right_occurrences, read_idle, Multiset.card_singleton]
    decide

theorem scope_name_images_are_disjoint (name : Name []) :
    ¬ ((∃ process, leftChoice process ∧ quote process = name) ∧
      (∃ process, rightChoice process ∧ quote process = name)) := by
  rintro ⟨⟨first, firstAdmitted, firstRead⟩, ⟨second, secondAdmitted, secondRead⟩⟩
  have same := quote_injective_on_exposed (left_bodies_exposed firstAdmitted)
    (right_bodies_exposed secondAdmitted) (firstRead.trans secondRead.symm)
  have carried : encodeEquationClass (quote (zero [])) ∈ channelSupport first := by
    rw [left_channel firstAdmitted]
    exact Set.mem_singleton _
  have alsoCarried : encodeEquationClass (quote (zero [])) ∈ channelSupport second :=
    same ▸ carried
  exact Set.disjoint_left.mp
    (complete_scope_channel_supports_are_disjoint first second firstAdmitted secondAdmitted)
    carried alsoCarried

theorem original_name_detection_is_not_automatic : ¬ NamesDetect leftChoice := by
  intro detected
  have member : idlePrime ∈ read (join repeatedLeft idle) := by
    rw [read_join, read_idle]
    exact Multiset.mem_add.mpr (Or.inr (Multiset.mem_singleton.mpr rfl))
  obtain ⟨name, carried⟩ := detected (join repeatedLeft idle) (Or.inr rfl) idlePrime member
  have empty : componentSupport idlePrime = ∅ := idle_support_empty
  rw [empty] at carried
  exact carried

theorem two_compositions_are_the_same_process :
    join repeatedLeft (join secondOutput idle) = join (join repeatedLeft idle) secondOutput := by
  apply read_injective []
  simp only [read_join]
  exact (congrArg (fun suffix => read repeatedLeft + suffix)
    (add_comm (read secondOutput) (read idle))).trans (add_assoc _ _ _).symm

theorem first_halves_are_different : repeatedLeft ≠ join repeatedLeft idle := by
  intro same
  have counts := congrArg (fun process => (read process).card) same
  rw [read_join, Multiset.card_add, left_occurrences, read_idle, Multiset.card_singleton] at counts
  cases counts

def ambiguousName : Name [] := quote (join repeatedLeft (join secondOutput idle))

/-- The separator lives in the complete typed rho quotient with actual quote and null equations. -/
theorem disjoint_scopes_and_channels_do_not_determine_quoted_halves :
    Composite leftChoice rightChoice ambiguousName ∧
      ∃ first second first' second' : Process [],
        leftChoice first ∧ rightChoice second ∧ leftChoice first' ∧ rightChoice second' ∧
        quote (join first second) = ambiguousName ∧
        quote (join first' second') = ambiguousName ∧ first ≠ first' := by
  refine ⟨⟨repeatedLeft, join secondOutput idle, Or.inl rfl, Or.inr rfl, rfl⟩,
    repeatedLeft, join secondOutput idle, join repeatedLeft idle, secondOutput,
    Or.inl rfl, Or.inr rfl, Or.inr rfl, Or.inl rfl, rfl, ?_, first_halves_are_different⟩
  exact congrArg quote two_compositions_are_the_same_process.symm

end Mettapedia.OSLF.Binding.RhoScopedScopeUnnamedControls
