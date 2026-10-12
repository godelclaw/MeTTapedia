import Mettapedia.OSLF.Syntax.RhoScopedFiniteReactions
import Mettapedia.OSLF.Syntax.RhoScopedParallelModalMetric

/-!
# Exact finite successor catalogues of original scoped rho least labels

The catalogue is independently formed from bounded constructor readings,
filtered by their computed missing partner, and then mapped to target classes.
Both directions compare it with the original root-instance IPO transitions.
This earns the finite-successor hypothesis of finitary modal adequacy on the
complete source quotient at every ambient scope and for either rule profile.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Binding.RhoScopedFiniteSuccessors

open RhoSchema RhoQuotationClassFibres RhoScopedParallelInventory
open RhoScopedParallelEvents RhoScopedParallelReactiveSystem RhoScopedParallelContexts
open RhoScopedReactionReadout RhoScopedFiniteReactions
open Mettapedia.GSLT.RedexRelativeCongruence

local instance (context : Ctx sig) : DecidableEq (Reading context) := Classical.decEq _
local instance (context : Ctx sig) : DecidableEq (Process context) := Classical.decEq _
local instance (context : Ctx sig) : DecidableEq (Prime context) := Classical.decEq _

def missing {context : Ctx sig} (first : Process context) (reading : Reading context) :
    Process context := write (read reading.source - read first)

def residual {context : Ctx sig} (first : Process context) (reading : Reading context) :
    Process context := write (read first - read reading.source)

def outcome {context : Ctx sig} (first : Process context) (reading : Reading context) :
    Process context := join reading.target (residual first reading)

def enabledReadings {context : Ctx sig} (admitted : SourceRule → Prop)
    (first label : Process context) : Finset (Reading context) :=
  (catalogue admitted (join first label)).filter (fun reading => missing first reading = label)

def successors {context : Ctx sig} (admitted : SourceRule → Prop)
    (first label : Process context) : Finset (Process context) :=
  (enabledReadings admitted first label).image (outcome first)

theorem root_missing {context : Ctx sig} {admitted : SourceRule → Prop}
    (first : Process context) (root : Root sourceRules admitted context) :
    missing first (rootReading root) = leastLabel first root := by
  simp only [missing, leastLabel, rootReading_source]

theorem root_outcome {context : Ctx sig} {admitted : SourceRule → Prop}
    (first : Process context) (root : Root sourceRules admitted context) :
    outcome first (rootReading root) = join root.target (reactionRemainder first root) := by
  simp only [outcome, residual, reactionRemainder, rootReading_source, rootReading_target]

theorem root_included {context : Ctx sig} {admitted : SourceRule → Prop}
    (first label : Process context) (root : Root sourceRules admitted context)
    (least : label = leastLabel first root) : read root.source ≤ read (join first label) := by
  rw [least, difference_square first root, read_join]
  exact Multiset.le_add_right _ _

theorem mem_successors_iff {context : Ctx sig} (admitted : SourceRule → Prop)
    (first label second : Process context) :
    second ∈ successors admitted first label ↔
      ActIPO (reactionRules sourceRules admitted) (arrow label) (arrow first) (arrow second) := by
  rw [successors, Finset.mem_image, actIPO_iff_computed]
  constructor
  · rintro ⟨reading, member, result⟩
    obtain ⟨catalogued, labelRead⟩ := Finset.mem_filter.mp member
    obtain ⟨_, allowed⟩ := (mem_catalogue admitted _ reading).mp catalogued
    let root := realize admitted reading allowed
    have readingRead : rootReading root = reading := rootReading_realize _ _ _
    refine ⟨root, ?_, ?_⟩
    · rw [← root_missing, readingRead]
      exact labelRead.symm
    · rw [← root_outcome, readingRead]
      exact result.symm
  · rintro ⟨root, least, targetRead⟩
    refine ⟨rootReading root, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      exact ⟨supplied_root_mem_catalogue (join first label) root
        (root_included first label root least), (root_missing first root).trans least.symm⟩
    · exact (root_outcome first root).trans targetRead.symm

theorem supplied_root_target_listed {context : Ctx sig} {admitted : SourceRule → Prop}
    (first label : Process context) (root : Root sourceRules admitted context)
    (least : label = leastLabel first root) :
    join root.target (reactionRemainder first root) ∈ successors admitted first label :=
  (mem_successors_iff admitted first label _).mpr
    ((actIPO_iff_computed _ _ _).mpr ⟨root, least, rfl⟩)

/-- Finiteness is earned from the actual source rules, including reflection. -/
theorem finite_successor_cover (admitted : SourceRule → Prop) (context : Ctx sig) :
    RhoScopedParallelModalAdequacy.Finitary.FiniteSuccessorCover sourceRules admitted context := by
  intro first label
  refine ⟨(successors admitted first label : Set (Process context)),
    (successors admitted first label).finite_toSet, ?_⟩
  intro root least
  refine ⟨join root.target (reactionRemainder first root),
    supplied_root_target_listed first label root least, ?_⟩
  exact ipoBisimilar_refl _ _

theorem finitary_adequacy (admitted : SourceRule → Prop) {context : Ctx sig}
    (first second : Process context) :
    RhoScopedParallelModalAdequacy.Finitary.LogicallyEquivalent sourceRules admitted first second ↔
      Bisimilar (rules := sourceRules) (admitted := admitted) first second :=
  RhoScopedParallelModalAdequacy.Finitary.logicallyEquivalent_iff_bisimilar sourceRules admitted
    (finite_successor_cover admitted context) first second

theorem finite_questions_complete (admitted : SourceRule → Prop) {context : Ctx sig}
    (first second : Process context) :
    RhoScopedParallelModalAdequacy.Finitary.LogicallyEquivalent sourceRules admitted first second ↔
      RhoScopedParallelModalAdequacy.Complete.LogicallyEquivalent sourceRules admitted first second :=
  RhoScopedParallelModalAdequacy.Finitary.logicallyEquivalent_iff_complete sourceRules admitted
    (finite_successor_cover admitted context) first second

theorem zero_distance_iff_bisimilar (admitted : SourceRule → Prop) {context : Ctx sig}
    (first second : Process context) :
    (RhoScopedParallelModalMetric.observations sourceRules admitted context).distance first second = 0 ↔
      Bisimilar (rules := sourceRules) (admitted := admitted) first second :=
  (RhoScopedParallelModalMetric.distance_eq_zero_iff sourceRules admitted first second).trans
    (finitary_adequacy admitted first second)

theorem metric_quotient_eq_iff_bisimilar (admitted : SourceRule → Prop) {context : Ctx sig}
    (first second : Process context) :
    Quotient.mk (RhoScopedParallelModalMetric.scheme sourceRules admitted context).setoid first =
      Quotient.mk (RhoScopedParallelModalMetric.scheme sourceRules admitted context).setoid second ↔
        Bisimilar (rules := sourceRules) (admitted := admitted) first second :=
  RhoScopedParallelModalMetric.quotient_eq_iff_bisimilar sourceRules admitted
    (finite_successor_cover admitted context) first second

end Mettapedia.OSLF.Binding.RhoScopedFiniteSuccessors
